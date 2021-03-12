

macro cxx_str(exprs...) return clang_str(__module__, __source__, :cxx, exprs...) end
macro cxx_cmd(exprs...) return clang_cmd(__module__, __source__, :cxx, exprs...) end


const CXX_HEADER = joinpath(@__DIR__, "$(nameof(@__MODULE__)).hpp")
header(::Type{Context{:cxx}}) = CXX_HEADER
Base.String(::Type{Context{:cxx}}) = "C++"




function getref(ctx::Type{Context{:cxx}}, str::AbstractString, mod::Union{Expr, Nothing} = nothing)
	function decorate(t, set)
		t = "volatile" in set ? :(Cvolatile{$(t)}) : t
		t = "restrict" in set ? :(Crestrict{$(t)}) : t
		t = "const"    in set ?    :(Cconst{$(t)}) : t
		return t
	end
	
	function sign(t, set)
		t =   "signed" in set ?   :(signed($(t))) : t
		t = "unsigned" in set ? :(unsigned($(t))) : t
		return t
	end
	
	function array(t, szs = [])
		m = match(C_ARRAY, t)
		if !isnothing(m)
			push!(szs, parse(Int, m.captures[2]))
			return array(m.captures[1], szs)
		end
		
		isempty(szs) && return nothing
		
		inner = getref(ctx, t, mod)
		isnothing(inner) && return nothing
		
		for sz in szs
			inner = decorate(:(Carray{$(inner), $(sz)}), ())
		end
		return inner
	end
	
	
	arr = array(str)
	isnothing(arr) || return arr
	
	m = match(C_POINTER, str)
	if !isnothing(m)
		inner = getref(ctx, m.captures[1], mod)
		isnothing(inner) || return decorate(:(Cptr{$(inner)}), (m.captures[2],))
	end
	
	m = match(C_FUNCPTR, str)
	if !isnothing(m)
		rettype  = getref(ctx, m.captures[1], mod)
		argtypes = isempty(m.captures[2]) ? () : map(arg -> getref(ctx, arg, mod), split(m.captures[2], ','))
		decor    = (m.captures[3],)
		conv     = isnothing(m.captures[4]) ? () : (QuoteNode(Symbol(m.captures[4])),)
		
		isnothing(rettype) || any(isnothing, argtypes) || return decorate(:(Cptr{Cfunction{$(rettype), Tuple{$(argtypes...)}, $(conv...)}}), decor)
	end
	
	m = match(C_PRIM, str)
	if !isnothing(m)
		prims = split(m.captures[1])
		
		if "_Complex" in prims
			if "double" in prims
				if "long" in prims
					return decorate(:(Ccomplex{Cdouble}), prims)
				else
					return decorate(:(Ccomplex{Clongdouble}), prims)
				end
			elseif "float" in prims
				return decorate(:(Ccomplex{Cfloat}), prims)
			end
		elseif "double" in prims
			if "long" in prims
				return decorate(:(Cdouble), prims)
			else
				return decorate(:(Clongdouble), prims)
			end
		elseif "float" in prims
			return decorate(:(Cfloat), prims)
		elseif "void" in prims
			return decorate(:(Cvoid), prims)
		elseif "bool" in prims || "_Bool" in prims
			return decorate(:(Cbool), prims)
		elseif "char" in prims
			return decorate(sign(:(Cchar), prims), prims)
		elseif "short" in prims
			return decorate(sign(:(Cshort), prims), prims)
		elseif "int" in prims
			return decorate(sign(:(Cint), prims), prims)
		elseif "long" in prims
			if count(isequal("long"), prims) > 1
				return decorate(sign(:(Clonglong), prims), prims)
			else
				return decorate(sign(:(Clong), prims), prims)
			end
		elseif "signed" in prims
			return decorate(:(signed(Cint)), prims)
		elseif "unsigned" in prims
			return decorate(:(unsigned(Cint)), prims)
		end
	end
	
	m = match(C_USER, str)
	if !isnothing(m)
		decor = (m.captures[1], m.captures[4])
		inner = getname(ctx, isnothing(m.captures[2]) ? "$(m.captures[3])" : "$(m.captures[2]) $(m.captures[3])")
		isnothing(inner) || return decorate(isnothing(mod) ? esc(inner) : :($(mod).$(inner)), decor)
	end
	
	strip(str) == "..." && return :(Cvariadic)
	
	m = match(C_MODULE, str)
	if !isnothing(m)
		str = m.captures[2]
		m   = Symbol(m.captures[1])
		return getref(ctx, str, isnothing(mod) ? esc(m) : :($(mod).$(m)))
	end
	
	return nothing
end



function gettype(ctx::Type{Context{:cxx}}, type::CXType; kwargs...)
	if type.kind == CXType_Void
		result = :(Cvoid)
	elseif type.kind == CXType_Bool
		result = :(Cbool)
	elseif type.kind == CXType_Char_S
		result = :(Cchar)
	elseif type.kind == CXType_Char_U
		result = :(Cuchar)
	elseif type.kind == CXType_SChar
		result = :(Cchar)
	elseif type.kind == CXType_UChar
		result = :(Cuchar)
	elseif type.kind == CXType_Short
		result = :(Cshort)
	elseif type.kind == CXType_Int
		result = :(Cint)
	elseif type.kind == CXType_Long
		result = :(Clong)
	elseif type.kind == CXType_LongLong
		result = :(Clonglong)
	elseif type.kind == CXType_UShort
		result = :(Cushort)
	elseif type.kind == CXType_UInt
		result = :(Cuint)
	elseif type.kind == CXType_ULong
		result = :(Culong)
	elseif type.kind == CXType_ULongLong
		result = :(Culonglong)
	elseif type.kind == CXType_Float
		result = :(Cfloat)
	elseif type.kind == CXType_Double
		result = :(Cdouble)
	elseif type.kind == CXType_LongDouble
		result = :(Clongdouble)
	elseif type.kind in (
		CXType_Typedef,
		CXType_Record,
		CXType_Elaborated,
		CXType_Enum,
	)
		decl = clang_getTypeDeclaration(type)
		t = clang_getCursorType(decl)
		result = gettype(ctx, string(t); kwargs...)
	elseif type.kind == CXType_Complex
		cplxtype = clang_getElementType(type)
		cplxtype = gettype(ctx, cplxtype; kwargs...)
		result = :(Ccomplex{$(cplxtype)})
	elseif type.kind == CXType_Pointer
		ptrtype = clang_getPointeeType(type)
		ptrtype = gettype(ctx, ptrtype; kwargs...)
		result = :(Cptr{$(ptrtype)})
	elseif type.kind == CXType_ConstantArray
		num = clang_getNumElements(type)
		arrtype = clang_getElementType(type)
		arrtype = gettype(ctx, arrtype; kwargs...)
		result = :(Carray{$(arrtype), $(num)})
	elseif type.kind == CXType_IncompleteArray
		arrtype = clang_getElementType(type)
		arrtype = gettype(ctx, arrtype; kwargs...)
		result = :(Carray{$(arrtype), 0})
	elseif type.kind == CXType_FunctionProto
		rettype = clang_getResultType(type)
		rettype = gettype(ctx, rettype; kwargs...)
		
		num = clang_getNumArgTypes(type)
		argtypes = map(1:num) do ind
			argtype = clang_getArgType(type, ind-1)
			return gettype(ctx, argtype; kwargs...)
		end
		argtypes = Bool(clang_isFunctionTypeVariadic(type)) ? [argtypes..., Cvariadic] : argtypes
		
		conv = clang_getFunctionTypeCallingConv(type)
		if conv == CXCallingConv_C
			conv = :(cdecl)
		else
			error("Unhandled calling convention $(conv)")
		end
		
		result = :(Cfunction{$(rettype), Tuple{$(argtypes...)}, $(QuoteNode(conv))})
	else
		error("Unhandle type $(type.kind)")
	end
	
	if Bool(clang_isVolatileQualifiedType(type))
		# TODO: not handled in get/set property etc. yet
		# result = :(Cvolatile{$(result)})
	end
	
	if Bool(clang_isRestrictQualifiedType(type))
		# TODO: not handled in get/set property etc. yet
		# result = :(Crestrict{$(result)})
	end
	
	# NOTE: always want Cconst around everything else to make life easier in get/set
	if Bool(clang_isConstQualifiedType(type))
		result = :(Cconst{$(result)})
	end
	
	return result
end



function getexprs(ctx::Context{:cxx}, cursor::CXCursor)
	exprs = []
	
	getblock(ctx).flags.skip && return exprs
	
	if cursor.kind == CXCursor_TranslationUnit
		append!(exprs, getexprs_tu(ctx, cursor))
	elseif cursor.kind in (
		CXCursor_VarDecl,
		CXCursor_FunctionDecl,
	)
		append!(exprs, getexprs_binding(ctx, cursor))
	elseif cursor.kind == CXCursor_UnexposedDecl
		for child in children(cursor)
			append!(exprs, getexprs(ctx, child))
		end
	elseif cursor.kind == CXCursor_InclusionDirective
		append!(exprs, getexprs_include(ctx, cursor))
	elseif !(cursor.kind in (
		CXCursor_StaticAssert,
		CXCursor_MacroDefinition,  # TODO: support this
		CXCursor_MacroInstantiation,  # TODO: support this
	))
		@warn "Not implemented $(cursor.kind):  $(string(cursor))"
	end
	
	return exprs
end



function getexprs_binding(ctx::Context{:cxx}, cursor::CXCursor)
	exprs = []
	
	exposed = clang_Cursor_getStorageClass(cursor)
	visible = clang_getCursorVisibility(cursor)
	linkage = clang_getCursorLinkage(cursor)
	if exposed in (
		CX_SC_None,
		CX_SC_Extern,
	) && visible in (
		CXVisibility_Default,
		CXVisibility_Protected,
	) && linkage in (
		CXLinkage_External,
	)
		name = string(cursor)
		lib = getlib(ctx, name)
		jlsym = getjl(ctx, name)
		sym = gettype(ctx, name)
		docs = getdocs(ctx, cursor)
		
		type = clang_getCursorType(cursor)
		if cursor.kind == CXCursor_VarDecl
			cb = :(Cbinding{$(gettype(ctx, type)), $(QuoteNode(Symbol(lib))), $(QuoteNode(Symbol(name)))})
			push!(exprs, getexprs(ctx, ((sym, jlsym, docs),), quote
				const $(sym) = $(cb)()
			end))
		elseif Bool(clang_Cursor_isFunctionInlined(cursor))
			getblock(ctx).flasg.quiet || @warn "Skipping inline function `$(name)`"
		else
			rettype = clang_getResultType(type)
			
			num = clang_Cursor_getNumArguments(cursor)
			args = map(1:num) do ind
				arg = clang_Cursor_getArgument(cursor, ind-1)
				
				argname = string(arg)
				argname = isempty(argname) ? getjl(ctx, "arg$(ind)") : gettype(ctx, argname)
				argtype = clang_getCursorType(arg)
				
				return argname => gettype(ctx, argtype)
			end
			args = Bool(clang_Cursor_isVariadic(cursor)) ? [args..., :($(getjl(ctx, :vararg))...) => :(Cvariadic)] : args
			
			conv = clang_getFunctionTypeCallingConv(type)
			if conv == CXCallingConv_C
				conv = :(cdecl)
			else
				error("Unhandled calling convention $(conv)")
			end
			
			func = getjl(ctx, :func)
			cb = :(Cbinding{Cfunction{$(gettype(ctx, rettype)), Tuple{$(map(last, args)...)}, $(QuoteNode(conv))}, $(lib), $(QuoteNode(Symbol(name)))})
			push!(exprs, getexprs(ctx, ((sym, jlsym, docs),), quote
				const $(sym) = $(cb)()
				($(func)::typeof($(sym)))($(map(first, args)...),) = funccall($(func), $(map(first, args)...),)
			end))
		end
	end
	
	return exprs
end
