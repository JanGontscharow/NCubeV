"""
SMTInterface
============

Abstractions over SMT solvers (Z3, CVC5, …) and AST translations used by the
Mosaic pipeline. Provides QF_LRA and QF_NRA contexts, translation helpers, and
the star-based counterexample filter per Lemma 12 (Appendix B.3).

Exports
- `smt_context`: Create and manage solver contexts
- `nl_feasible`, `lin_feasible`: Feasibility checks (with optional unsat cores)

See also: `SMTInterface.AST2SMT`, `SMTInterface.StarFilter`.
"""
module SMTInterface
	using MLStyle
	using TimerOutputs

	using ..Util
	using ..AST
	using ..VerifierInterface
	import ..Config.SMT_SOLVER
	import ..Config.TIMER

	using Satisfiability: Z3 as SatZ3, Solver as SatSolver

	export smt_context, nl_feasible, nl_feasible_init, ast2sat

	USE_CORES = true

	if SMT_SOLVER == "Z3"
		include("Z3/Main.jl")
	elseif SMT_SOLVER == "CVC5"
		include("CVC5/Main.jl")
	#elseif SMT_SOLVER == "dreal"
	#	include("dreal/Main.jl")
	else
		error("Unknown SMT solver: " + SMT_SOLVER)
	end


	include("AST2SMT.jl")
	include("AST2Sat.jl")
	include("Base.jl")
	include("StarFilter.jl")

	"""
		nl_feasible(constraints::Vector{Union{Formula}}, ctx, variables, conflicts; print_model=false) -> Bool

	Check feasibility of a set of (possibly nonlinear) constraints under QF_NRA.
	Uses activation literals to optionally extract an unsat core into `conflicts`
	(indices of `constraints`). Returns `true` if satisfiable or unknown.
	"""
	function nl_feasible(constraints :: Vector{Union{Formula}}, ctx, variables,conflicts;print_model=false)
		res = smt_solver(ctx) do s
			smt_internal_set(s,"unsat-core",true)
			conflict_clauses = Dict()
			vars = ExprVector(ctx)
			@timeit TIMER "SMTprep" begin
				for (i,c) in enumerate(constraints)
					additional = []
					smt_cache = Dict()
					translated = ast2smt(c, variables, additional, smt_cache)
					#print_msg(translated)
					conflict_var = bool_const(ctx, "c" * string(i))
					smt_internal_add(s, Z3.implies(conflict_var,translated))
					conflict_clauses[string(conflict_var)] = i
					push!(vars, conflict_var)
					for a in additional
						smt_internal_add(s, a)
					end
				end
			end
			
			res1 = smt_internal_check(s, vars)
			#-----------------------------
			additional = []
			@satvariable(x[1:length(variables)], Real)
			cons_trans = map(con -> ast2sat(con, x, additional, Dict()), constraints)
			expr = Sat.and(cons_trans...) #∧
			#	Sat.and([c ⟹ con for (c,con) in zip(C, cons_trans)])
			#expr = Sat.and([c ⟹ con for (c,con) in zip(C, cons_trans)])
			
			!isempty(additional) && (expr = expr ∧ Satisfiability.and(additional...)) 

			# If expr simplified to a native Bool, wrap it back into an SMT expression
			if expr isa Bool
				expr = Satisfiability.__wrap_const(expr)
			end

			res = sat!(expr, solver=SatZ3(), logic="QF_NRA")
			if smt_internal_is_sat(res1) && (res != :SAT)
				@warn "[nl_feasible] Discrepancy between SMT and Sat solver results."
				@show constraints
				@show res
			elseif smt_internal_is_unsat(res1) && (res == :SAT)
				@warn "[nl_feasible] Discrepancy between SMT and Sat solver results."
				@show constraints
				@show res
				@show expr
				#@assert false "SMT and Sat solver results disagree."
			else
				println("[nl_feasible] SMT and Sat solver results agree $(res).")
			end
	
			@timeit TIMER "SMTprep" begin
			#conflicts = []
			if res == :SAT
				if print_model
					smt_print_model(s)
				end
			elseif res != :UNSAT
				print_msg("[SMT] SMT returned status: ", res)
			else # unsat
				#print_msg("[SMT] Conflict:")
				if USE_CORES
					for c in unsat_core(s)
						#print_msg("[SMT] ", c)
						#print_msg("[SMT] ", constraints[conflict_clauses[string(c)]])
						push!(conflicts,conflict_clauses[string(c)])
					end
				else
					for (i,_) in enumerate(constraints)
						push!(conflicts,i)
					end
				end
			end
			end

			return res
		end
		return res != :UNSAT
	end


	"""
		lin_feasible(constraints::Vector{LinearConstraint}, ctx, variables, conflicts; print_model=false) -> Bool

	Check feasibility of linear constraints under QF_LRA with activation literals
	for unsat core extraction. Returns `true` if satisfiable or unknown.
	"""
	function lin_feasible(constraints :: Vector{LinearConstraint}, ctx, variables,conflicts;print_model=false)
		res = smt_solver(ctx;theory="qflra") do s
			smt_internal_set(s,"unsat-core",true)
			conflict_clauses = Dict()
			vars = ExprVector(ctx)
			@timeit TIMER "SMTprep" begin
				for (i,c) in enumerate(constraints)
					additional = []
					smt_cache = Dict()
					translated = ast2smt(c, variables, additional, smt_cache)
					#print_msg(translated)
					conflict_var = bool_const(ctx, "c" * string(i))
					smt_internal_add(s, Z3.implies(conflict_var,translated))
					conflict_clauses[string(conflict_var)] = i
					push!(vars, conflict_var)
					for a in additional
						smt_internal_add(s, a)
					end
				end
			end
			
			res1 = smt_internal_check(s, vars)

			#-----------------------------
			additional = []
			@satvariable(x[1:length(variables)], Real)
			cons_trans = map(con -> ast2sat(con, x, additional, Dict()), constraints)
			expr = Sat.and(cons_trans...) #∧
			#	Sat.and([c ⟹ con for (c,con) in zip(C, cons_trans)])
			#expr = Sat.and([c ⟹ con for (c,con) in zip(C, cons_trans)])
			
			!isempty(additional) && (expr = expr ∧ Satisfiability.and(additional...)) 

			# If expr simplified to a native Bool, wrap it back into an SMT expression
			if expr isa Bool
				expr = Satisfiability.__wrap_const(expr)
			end

			res = sat!(expr, solver=SatZ3(), logic="QF_LRA")
			if smt_internal_is_sat(res1) && (res != :SAT)
				@warn "[lin_feasible] Discrepancy between SMT and Sat solver results."
				@show constraints
				@show res
			elseif smt_internal_is_unsat(res1) && (res == :SAT)
				@warn "[lin_feasible] Discrepancy between SMT and Sat solver results."
				@show constraints
				@show res
				@show expr
				@assert false "SMT and Sat solver results disagree."
			else
				#println("[lin_feasible] SMT and Sat solver results agree $(res).")
			end
			
			@timeit TIMER "SMTprep" begin
			#conflicts = []
			if res == :SAT
				if print_model
					smt_print_model(s)
				end
			elseif res != :UNSAT
				print_msg("[SMT] SMT returned status: ", res)
			else # unsat
				#print_msg("[SMT] Conflict:")
				if USE_CORES
					for c in unsat_core(s)
						#print_msg("[SMT] ", c)
						#print_msg("[SMT] ", constraints[conflict_clauses[string(c)]])
						push!(conflicts,conflict_clauses[string(c)])
					end
				else
					for (i,_) in enumerate(constraints)
						push!(conflicts,i)
					end
				end
			end
			end

			return res
		end
		return res != :UNSAT
	end
end