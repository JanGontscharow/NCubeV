using Satisfiability
Sat = Satisfiability


"""
AST-to-SMT translation utilities
--------------------------------

Translate NCubeV AST nodes to solver-native expressions used by SMT backends.
The functions here are solver-agnostic and produce intermediate `Formula`
structures ready to be consumed by backend-specific translators (e.g., Z3 in
`SMTInterface/Z3/AST2Z3.jl`).

Key responsibilities:
- Construct input/output box constraints from `NormalizedQuery`
- Flatten piecewise-linear conjunctions (`PwlConjunction`) into AND terms
- Convert semi-linear constraints to linear atoms

See also:
- `SMTInterface.StarFilter` for counterexample filtering logic (Lemma 12)
- `SMTInterface.Z3.AST2Z3` for backend-specific lowering
"""
function ast2sat(q :: NormalizedQuery, variables, additional)
	conjunction = Formula[]
	num_inputs = length(q.input_bounds)
	num_outputs = length(q.output_bounds)
	for (i,b) in enumerate(q.input_bounds)
		push!(conjunction, Atom(LessEq, b[1], Variable("x"*string(i),nothing,i)))
		push!(conjunction, Atom(LessEq, Variable("x"*string(i),nothing,i), b[end]))
	end
	for (i,b) in enumerate(q.output_bounds)
		push!(conjunction, Atom(LessEq,b[1], Variable("x"*string(num_inputs + i),nothing,num_inputs + i)))
		push!(conjunction, Atom(LessEq, Variable("x"*string(num_inputs + i),nothing,num_inputs + i), b[end]))
	end
	encoded_input =pwl2term(q.input_constraints)
	if !isnothing(encoded_input)
		push!(conjunction, encoded_input)
	end
	disjuntion = Formula[]
	for c in q.mixed_constraints
		push!(disjuntion, pwl2term(c))
	end
	if length(disjuntion) > 1
		push!(conjunction, CompositeFormula(Or,disjuntion))
	else
		push!(conjunction, disjuntion[1])
	end
	if length(conjunction)==1
		return ast2sat(conjunction[1], variables, additional)
	else
		return ast2sat(CompositeFormula(And,conjunction), variables, additional)
	end
end

"""
	pwl2term(pwl::PwlConjunction) -> Union{Formula,Nothing}

Flatten a piecewise-linear conjunction into a single formula by combining
variable bounds, linear constraints, and semi-linear constraints as an AND.
Returns `nothing` if the conjunction is empty.
"""

"""
	ast2sat(semi::SemiLinearConstraint, variables, additional)

Convert a semi-linear constraint (linear part plus weighted approx queries)
to an SMT atom by substituting the semi-linear components into the
left-hand side term and creating a strict/weak inequality depending on
`semi.equality`.

Notes:
- Coefficients are rationalized to improve solver stability.
"""
function ast2sat(semi :: SemiLinearConstraint, variables, additional)
	term = TermNumber(0.0)
	for (i,c) in enumerate(semi.coefficients)
		term = CompositeTerm(Add, Term[term, rationalize(Int32,BigFloat(c)) * Variable("x"*string(i),nothing,i)])
	end
	for (approx_query, coeff) in semi.semilinears
		term = CompositeTerm(Add, Term[term, rationalize(Int32,BigFloat(coeff)) * approx_query.term])
	end
	if semi.equality
		return ast2sat(Atom(LessEq, term, rationalize(Int32,BigFloat(semi.bias))), variables, additional)
	else
		return ast2sat(Atom(Less, term, rationalize(Int32,BigFloat(semi.bias))), variables, additional)
	end
end



# TODO(steuber): Floating Point Correctness?
function ast2sat(f :: CompositeFormula, variables, additional, smt_cache=Dict())
	if haskey(smt_cache, f)
		return smt_cache[f]
	end
	arguments = map(x -> ast2sat(x, variables, additional, smt_cache), f.args)
	res = @match f.connective begin
		Not => Sat.not(arguments[1])
		And => Sat.and(arguments...)
		Or => Sat.or(arguments...)
		Implies => Sat.implies(arguments[1],arguments[2])
		ITE => Sat.ite(arguments[1],arguments[2],arguments[3])
	end

	smt_cache[f] = res
	return res
end
function ast2sat(f :: TrueAtom, variables, additional, smt_cache)
	@satvariable(t, Bool)
	if haskey(smt_cache, f)
		return smt_cache[f]
	end
    res = Sat.__wrap_const(true)
	smt_cache[f] = res
	return res
end
function ast2sat(f :: FalseAtom, variables, additional, smt_cache)
	@satvariable(t, Bool)
	if haskey(smt_cache, f)
		return smt_cache[f]
	end
    res = Sat.__wrap_const(false)
	smt_cache[f] = res
	return res
end
"""
	ast2sat(f::LinearConstraint, variables, additional, smt_cache)

Encode a linear (or weakly linear) constraint `A*x [</<=] b` as a Sat
comparison. Coefficients and bias are rationalized for stability.
"""
#TODO(steuber): FLOAT INCORRECTNESS
function ast2sat(f :: LinearConstraint, variables, additional, smt_cache=Dict())
	
	if haskey(smt_cache, f)
		return smt_cache[f]
	end
	
	coeff = map(c -> ast2sat(TermNumber(c), variables, additional, smt_cache), f.coefficients)
	bias = ast2sat(TermNumber(f.bias), variables, additional, smt_cache)
	n = length(coeff) # variables may have more entries than coefficients (input constraints)


	# not working, due to incorrect behavior of multiplication with 0.0
	lincomb = sum(coeff .* variables[1:n])
	#lincomb = 0.0
	#for i in 1:n
	#	if (coeff[i] != 0.0) && (variables[i].value != 0.0)
	#		lincomb += coeff[i] * variables[i]
	#	end
	#end

	res = f.equality ? lincomb ≤ bias : lincomb < bias
	
	smt_cache[f] = res
	return res
end

"""
	ast2sat(t::LinearTerm, variables, additional, smt_cache)

Lower a linear term into a Sat arithmetic expression.
"""
function ast2sat(t :: LinearTerm, variables, additional, smt_cache)
	
	if haskey(smt_cache, t)
		return smt_cache[t]
	end

	#@info "linear-term: $t"

	coeff = map(c -> ast2sat(TermNumber(c), variables, additional, smt_cache), t.coefficients)
	for c in coeff
		if isa(c, Sat.NumericExpr)
			c = c.value
		end
	end
	
	#@info "coeff: $coeff"
	
	bias = ast2sat(TermNumber(t.bias), variables, additional, smt_cache)
	n = length(coeff) # variables may have more entries than coefficients (input constraints)
	
	#@info "vec: $(coeff .* variables[1:n])"

	# not working, due to incorrect behavior of multiplication with 0.0
	lincomb = sum(coeff .* variables[1:n])
	#lincomb = 0.0
	#for i in 1:n
	#	if coeff[i] != 0.0
	#		lincomb += coeff[i] * variables[i]
	#	end
	#end
	#@info "lincomb: $lincomb"

	res = lincomb + bias

	#@info "res: $res"

	smt_cache[t] = res


	return res
end

"""
	ast2sat(f::ApproxNode, ...)

Forward translation to the underlying formula carried by an approximation node.
"""
function ast2sat(f :: ApproxNode, variables, additional, smt_cache)
	if haskey(smt_cache, f)
		return smt_cache[f]
	end
	res = ast2sat(f.formula, variables, additional, smt_cache)
	smt_cache[f] = res
	return res
end
"""
	ast2sat(f::Atom, ...)

Translate atomic comparisons by recursively lowering both sides and applying
the respective Sat comparator.
"""
function ast2sat(f :: Atom, variables, additional, smt_cache=Dict())
	if haskey(smt_cache, f)
		return smt_cache[f]
	end
	termLeft = ast2sat(f.left, variables, additional, smt_cache)
	termRight = ast2sat(f.right, variables, additional, smt_cache)
	res = @match f.comparator begin
		Less => termLeft < termRight
		LessEq => termLeft <= termRight
		Greater => termLeft > termRight
		GreaterEq => termLeft >= termRight
		Eq => termLeft == termRight
		Neq => Sat.distinct(termLeft, termRight)
	end
	smt_cache[f] = res
	return res
end


function ast2sat_smt_pow(base, exp, variables=[], additional=[], smt_cache=Dict())
	@assert isa(exp, TermNumber) "Exponent must be a TermNumber."
	@assert isa(base, TermNumber) || isa(base, Variable) "Base must be a TermNumber, Variable."
	
	num = exp.value.num
	den = exp.value.den

	if den == 1
		if isa(base, TermNumber)
			return ast2sat(base^exp, variables, additional, smt_cache)
		else
			var = ast2sat(base, variables, additional, smt_cache)
			if num > 0
				# xⁿ = x ⋅ x ⋯ x
				return foldl(*, fill(var, num))
			elseif num < 0
				# x⁻ⁿ = 1 / (x ⋅ x ⋯ x)
				return 1.0 / foldl(*, fill(var, -num))
			else
				return 1.0
			end		
		end
	else
		@assert false "Non-integer exponents not supported in SMT backend yet."
		# TODO(steuber): Implement roots again (but probably hard for SMT solver anyway...)
	end
end

"""
	ast2sat(f::CompositeTerm, ...)

Handle arithmetic combinations Add/Sub/Mul/Div/Pow/Neg. For non-integer
exponents, guards restrict the domain to non-negative and fall back to 0 otherwise.
"""
function ast2sat(f :: CompositeTerm, variables, additional, smt_cache)
	if haskey(smt_cache, f)
		return smt_cache[f]
	end
	if f.operation ≠ Pow
		arguments = map(x -> ast2sat(x, variables, additional, smt_cache), f.args)
		res = @match f.operation begin
			Add => +(arguments...)
			Sub => -(arguments...)
			Mul => *(arguments...)
			Div => /(arguments...)
			Neg => return -arguments[1]
		end
	else
		@assert length(f.args) == 2 "Pow operation requires exactly two arguments."
		res = ast2sat_smt_pow(f.args..., variables, additional, smt_cache)
	end
	
	smt_cache[f] = res
	return res
end
function ast2sat(v :: Variable, variables, additional, smt_cache)
	return variables[v.position]
end
function ast2sat(n::TermNumber, variables, additional, smt_cache)
	x = Float64(n.value)
	x_str = string(x)

	if !contains(x_str, "e")
		return x
	else
		@warn "$(x) contains scientific notation. adding shield variable."
		@satvariable(t_shield, Real)
		push!(additional, t_shield == 1.0)

		parts = split(x_str, 'e')
		coeff = parse(Float64, parts[1])
		exponent = parse(Int, parts[2])

		@assert exponent < 0 "Only negative exponents are supported for shield variables."
		
		divisor = 10.0^(-exponent)

		@assert !contains(string(divisor), "e") "Shield variable divisor cannot be in scientific notation."

		return (coeff / (divisor * t_shield))
	end
	
end


