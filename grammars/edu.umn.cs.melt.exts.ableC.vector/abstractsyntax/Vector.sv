grammar edu:umn:cs:melt:exts:ableC:vector:abstractsyntax;

imports silver:langutil;
imports silver:langutil:pp;

imports edu:umn:cs:melt:ableC:abstractsyntax:host hiding vectorType;
imports edu:umn:cs:melt:ableC:abstractsyntax:construction;
imports edu:umn:cs:melt:ableC:abstractsyntax:env;
imports edu:umn:cs:melt:ableC:abstractsyntax:overloadable as ovrld;
--imports edu:umn:cs:melt:ableC:abstractsyntax:debug;

imports edu:umn:cs:melt:exts:ableC:templating;
imports edu:umn:cs:melt:exts:ableC:string;
imports edu:umn:cs:melt:exts:ableC:constructor;

-- Vector initialization
abstract production newVector
top::Expr ::= sub::Type args::Exprs
{
  top.pp = pp"new vector<${sub.lpp}${sub.rpp}>(${ppImplode(pp", ", args.pps)})";
  
  local expectedSizeType::Type =
    builtinType(nilQualifier(), unsignedType(longType()));
  local expectedAllocatorType::Type =
    functionType(
      pointerType(
        nilQualifier(),
        builtinType(nilQualifier(), voidType())),
      protoFunctionType([builtinType(nilQualifier(), unsignedType(longType()))], false),
      nilQualifier());
  local expectedReallocatorType::Type =
    functionType(
      pointerType(
        nilQualifier(),
        builtinType(nilQualifier(), voidType())),
      protoFunctionType(
        [pointerType(nilQualifier(), builtinType(nilQualifier(), voidType())),
         builtinType(nilQualifier(), unsignedType(longType()))],
        false),
      nilQualifier());
  local expectedDeallocatorType::Type =
    functionType(
      builtinType(nilQualifier(), voidType()),
      protoFunctionType(
        [pointerType(nilQualifier(), builtinType(nilQualifier(), voidType()))],
        false),
      nilQualifier());
  local localErrors::[Message] =
    args.errors ++
    checkVectorHeaderDef("new_vector", top.location, top.env) ++
    case args of
    | consExpr(size, _) ->
      if typeAssignableTo(expectedSizeType, size.typerep) then []
      else [err(size.location, s"Size must have type unsigned long (got ${showType(size.typerep)})")]
    | _ -> []
    end ++
    case args of
    | consExpr(_, consExpr(init, _)) ->
      if typeAssignableTo(sub, init.typerep) then []
      else [err(init.location, s"Initial value must have type ${showType(sub)} (got ${showType(init.typerep)})")]
    | _ -> []
    end ++
    case args of
    | consExpr(_, consExpr(_, consExpr(allocator, _))) ->
      if typeAssignableTo(expectedAllocatorType, allocator.typerep) then []
      else [err(allocator.location, s"Allocator must have type void *(unsigned long) (got ${showType(allocator.typerep)})")]
    | _ ->
      if !null(lookupValue("GC_malloc", top.env))
      then []
      else [err(top.location, "Vector expression lacking an explicit allocator requires <gc.h> to be included.")]
    end ++
    case args of
    | consExpr(_, consExpr(_, consExpr(_, consExpr(reallocator, _)))) ->
      if typeAssignableTo(expectedReallocatorType, reallocator.typerep) then []
      else [err(reallocator.location, s"Reallocator must have type void *(void *, unsigned long) (got ${showType(reallocator.typerep)})")]
    | _ -> []
    end ++
    case args of
    | consExpr(_, consExpr(_, consExpr(_, consExpr(_, consExpr(deallocator, _))))) ->
      if typeAssignableTo(expectedDeallocatorType, deallocator.typerep) then []
      else [err(deallocator.location, s"Deallocator must have type void(void *) (got ${showType(deallocator.typerep)})")]
    | _ -> []
    end ++
    case args of
    | consExpr(_, consExpr(_, consExpr(_, consExpr(_, consExpr(_, consExpr(_, _)))))) ->
      [err(top.location, s"Too many arguments in vector expression")]
    | _ -> []
    end;
  
  local size::Expr =
    case args of
    | consExpr(size, _) -> size
    | _ -> ableC_Expr {0}
    end;
  local init::Expr =
    case args of
    | consExpr(_, consExpr(init, _)) -> init
    | _ -> ableC_Expr { ($directTypeExpr{sub}){0} }
    end;
  local allocator::Expr =
    case args of
    | consExpr(_, consExpr(_, consExpr(allocator, _))) -> allocator
    | _ -> ableC_Expr {GC_malloc}
    end;
  local reallocator::Expr =
    case args of
    | consExpr(_, consExpr(_, consExpr(_, consExpr(reallocator, _)))) -> reallocator
    | _ -> ableC_Expr {GC_realloc}
    end;
  local deallocator::Expr =
    case args of
    | consExpr(_, consExpr(_, consExpr(_, consExpr(_, consExpr(deallocator, _))))) -> deallocator
    | _ -> ableC_Expr {(void (*)(void*))0}
    end;
  local fwrd::Expr =
    ableC_Expr { inst new_vector<$directTypeExpr{sub}>($Expr{size}, $Expr{init}, $Expr{allocator}, $Expr{reallocator}, $Expr{deallocator}) };
  
  forwards to mkErrorCheck(localErrors, fwrd);
}

abstract production vectorInitializer
top::Initializer ::= i::InitList
{
  top.pp = ppConcat([text("{"), ppImplode(text(", "), i.pps), text("}")]);
  
  i.vectorInitType =
    case top.expectedType of
    | extType(_, vectorType(sub)) -> sub
    | _ -> error("Vector initializer expected vector type")
    end;

  -- Needed by flow analysis
  i.expectedType = top.expectedType;
  i.expectedTypes = [];
  i.initIndex = 0;
  i.tagEnvIn = emptyEnv();

  forwards to
    exprInitializer(
      warnExpr(
        i.vectorInitErrors,
        constructVector(
          typeName(directTypeExpr(i.vectorInitType), baseTypeExpr()),
          nilExpr(), foldExpr(i.vectorInitExprs),
          location=top.location),
        location=top.location),
      location=top.location);
}

autocopy attribute vectorInitType::Type occurs on InitList, Init;
monoid attribute vectorInitExprs::[Expr] with [], ++ occurs on InitList, Init;
monoid attribute vectorInitErrors::[Message] with [], ++ occurs on InitList, Init;
propagate vectorInitExprs, vectorInitErrors on InitList;

aspect production positionalInit
top::Init ::= i::Initializer
{
  top.vectorInitExprs :=
    [ableC_Expr { ({$directTypeExpr{top.vectorInitType} _val = $Initializer{i}; _val;}) }];
  top.vectorInitErrors := [];
}

aspect production designatedInit
top::Init ::= d::Designator i::Initializer
{
  top.vectorInitExprs := [];
  top.vectorInitErrors := [err(i.location, "Designated init not permitted in vector initializer")];
}

abstract production constructVector
top::Expr ::= sub::TypeName args::Exprs e::Exprs
{
  top.pp = pp"vec<${sub.pp}>(${ppImplode(pp", ", args.pps)})[${ppImplode(pp", ", e.pps)}]";
  
  local localErrors::[Message] =
    sub.errors ++ args.errors ++ e.errors ++
    e.vectorInitErrors ++
    checkVectorHeaderDef("new_vector", top.location, top.env);
  
  sub.env = globalEnv(top.env);
  args.env = addEnv(sub.defs, sub.env);
  e.env = addEnv(args.defs, args.env);
  e.argumentPosition = 0;
  e.vectorInitType = sub.typerep;
  
  local fwrd::Expr =
    ableC_Expr {
      ({$Decl{decls(foldDecl(sub.decls))}
        $BaseTypeExpr{vectorTypeExpr(nilQualifier(), sub, builtin)} _vec =
          $Expr{
            newVector(
              sub.typerep,
              consExpr(
                mkIntConst(e.count, builtin),
                consExpr(
                  ableC_Expr { ($directTypeExpr{sub.typerep})($directTypeExpr{sub.typerep.host}){0} },
                  args)),
              location=top.location)};
        $Stmt{e.vectorInitTrans}
        _vec;})
    };
  
  forwards to mkErrorCheck(localErrors, fwrd);
}

abstract production inferredConstructVector
top::Expr ::= args::Exprs e::Exprs
{
  top.pp = pp"vec(${ppImplode(pp", ", args.pps)})[${ppImplode(pp", ", e.pps)}]";
  
  local subType::Type = head(e.typereps);
  
  local localErrors::[Message] =
    args.errors ++ e.errors ++
    (if e.count == 0
     then [err(top.location, "Can't infer type argument for empty vector")]
     else e.vectorInitErrors) ++
    checkVectorHeaderDef("new_vector", top.location, top.env);
  
  e.argumentPosition = 0;
  e.vectorInitType = subType;
  
  local fwrd::Expr =
    ableC_Expr {
      ({$BaseTypeExpr{
        vectorTypeExpr(
          nilQualifier(),
          typeName(directTypeExpr(subType), baseTypeExpr()),
          builtin)} _vec =
          $Expr{
            newVector(
              subType,
              consExpr(
                mkIntConst(e.count, builtin),
                consExpr(
                  ableC_Expr { ($directTypeExpr{subType})($directTypeExpr{subType.host}){0} },
                  args)),
              location=top.location)};
        $Stmt{e.vectorInitTrans}
        _vec;})
    };
  
  forwards to mkErrorCheck(localErrors, fwrd);
}

abstract production deleteVector
top::Stmt ::= e::Expr
{
  top.pp = pp"delete ${e.pp};";
  top.functionDefs := [];
  
  local localErrors :: [Message] =
    e.errors ++
    checkVectorHeaderDef("delete_vector", e.location, top.env);
  
  local subType::Type = vectorSubType(e.typerep);
  local fwrd::Stmt =
    ableC_Stmt { inst delete_vector<$directTypeExpr{subType}>($Expr{e}); };
  
  forwards to if !null(localErrors) then warnStmt(localErrors) else fwrd;
}


attribute vectorInitType, vectorInitErrors occurs on Exprs;
monoid attribute vectorInitTrans::Stmt with nullStmt(), seqStmt occurs on Exprs;
propagate vectorInitErrors, vectorInitTrans on Exprs;

aspect production consExpr
top::Exprs ::= h::Expr t::Exprs
{
  top.vectorInitErrors <- t.vectorInitErrors;
  top.vectorInitTrans <-
    ableC_Stmt {
      _vec[$intLiteralExpr{top.argumentPosition}] = $Expr{h};
    };
}

abstract production concatVector
top::Expr ::= e1::Expr e2::Expr
{
  top.pp = pp"${e1.pp} + ${e2.pp}";
  
  local subType::Type = vectorSubType(e1.typerep);
  local localErrors::[Message] =
    e1.errors ++ e2.errors ++
    checkVectorHeaderDef("copy_vector", top.location, top.env) ++
    checkVectorType(subType, e1.typerep, "concat", top.location) ++
    checkVectorType(subType, e2.typerep, "concat", top.location);
  
  local vecTempName::String = "_vec_" ++ toString(genInt());
  local fwrd::Expr =
    ableC_Expr {
      ({$directTypeExpr{e1.typerep} $name{vecTempName} = $Expr{copyVector(e1, location=builtin)};
        $Expr{
          extendVector(
            declRefExpr(name(vecTempName, location=builtin), location=builtin),
            e2,
            location=builtin)};
        $name{vecTempName};})
    };
  
  forwards to mkErrorCheck(localErrors, fwrd);
}

abstract production equalsVector
top::Expr ::= e1::Expr e2::Expr
{
  top.pp = pp"${e1.pp} == ${e2.pp}";
  
  local subType::Type = vectorSubType(e1.typerep);
  local localErrors::[Message] =
    e1.errors ++ e2.errors ++
    checkVectorHeaderDef("equals_vector", top.location, top.env) ++
    checkVectorType(subType, e1.typerep, "==", top.location) ++
    checkVectorType(subType, e2.typerep, "==", top.location);
    -- TODO: Check that == is defined for subType
  local fwrd::Expr = ableC_Expr { inst equals_vector<$directTypeExpr{subType}>($Expr{e1}, $Expr{e2}) };
  
  forwards to mkErrorCheck(localErrors, fwrd);
}

abstract production addressOfSubscriptVector
top::Expr ::= e1::Expr e2::Expr
{
  top.pp = pp"${e1.pp}[${e2.pp}]";
  
  local subType::Type = vectorSubType(e1.typerep);
  local localErrors::[Message] =
    e1.errors ++ e2.errors ++
    checkVectorHeaderDef("_check_index_vector", top.location, top.env) ++
    checkVectorType(subType, e1.typerep, "[]", top.location) ++
    if e2.typerep.isIntegerType
    then []
    else [err(e2.location, s"Vector index must have integer type, but got ${showType(e2.typerep)}")];
  
  local vecTempName::String = "_vec_" ++ toString(genInt());
  local indexTempName::String = "_index_" ++ toString(genInt());
  local fwrd::Expr =
    ableC_Expr {
      proto_typedef _vector_s;
      ({$directTypeExpr{e1.typerep} $name{vecTempName} = $Expr{e1};
        $directTypeExpr{e2.typerep} $name{indexTempName} = $Expr{e2};
        inst _check_index_vector<$directTypeExpr{subType}>($name{vecTempName}, $name{indexTempName});
        ((inst _vector_s<$directTypeExpr{subType}> *)$name{vecTempName})->contents + $name{indexTempName};})
    };
  
  forwards to mkErrorCheck(localErrors, fwrd);
}

abstract production callMemberVector
top::Expr ::= lhs::Expr deref::Boolean rhs::Name a::Exprs
{
  
  forwards to
    case rhs.name, a of
      "append", consExpr(e, nilExpr()) -> appendVector(lhs, e, location=top.location)
    | "insert", consExpr(e1, consExpr(e2, nilExpr())) -> insertVector(lhs, e1, e2, location=top.location)
    | "extend", consExpr(e, nilExpr()) -> extendVector(lhs, e, location=top.location)
    | "copy", nilExpr() -> copyVector(lhs, location=top.location)
    | n, _ -> errorExpr([err(rhs.location, s"Vector does not have field ${n} with ${toString(a.count)} parameters")], location=top.location)
    end;
}

abstract production copyVector
top::Expr ::= e::Expr
{
  top.pp = pp"${e.pp}.copy()";
  
  local subType::Type = vectorSubType(e.typerep);
  local localErrors::[Message] =
    e.errors ++
    checkVectorHeaderDef("copy_vector", top.location, top.env) ++
    checkVectorType(subType, e.typerep, "vector copy", top.location);
  local fwrd::Expr = ableC_Expr { inst copy_vector<$directTypeExpr{subType}>($Expr{e}) };
  
  forwards to mkErrorCheck(localErrors, fwrd);
}

abstract production appendVector
top::Expr ::= lhs::Expr elem::Expr
{
  top.pp = pp"${lhs.pp}.append(${elem.pp})";
  
  local subType::Type = vectorSubType(lhs.typerep);
  local localErrors::[Message] =
    lhs.errors ++ elem.errors ++
    checkVectorHeaderDef("append_vector", top.location, top.env) ++
    checkVectorType(subType, lhs.typerep, "append", top.location) ++
    if !typeAssignableTo(subType, elem.typerep)
    then [err(top.location, s"Appended type must be the same as vector sub-type, got ${showType(subType)} and ${showType(elem.typerep)}")]
    else [];
  
  local fwrd::Expr = ableC_Expr { inst append_vector<$directTypeExpr{subType}>($Expr{lhs}, $Expr{elem}) };
  
  forwards to mkErrorCheck(localErrors, fwrd);
}

abstract production insertVector
top::Expr ::= lhs::Expr index::Expr elem::Expr
{
  top.pp = pp"${lhs.pp}.insert(${index.pp}, ${elem.pp})";
  
  local subType::Type = vectorSubType(lhs.typerep);
  local localErrors::[Message] =
    lhs.errors ++ index.errors ++ elem.errors ++
    checkVectorHeaderDef("insert_vector", top.location, top.env) ++
    checkVectorType(subType, lhs.typerep, "insert", top.location) ++
    (if index.typerep.isIntegerType
     then []
     else [err(index.location, s"Vector insertion index must have integer type, but got ${showType(index.typerep)}")]) ++
    (if !typeAssignableTo(subType, elem.typerep)
     then [err(top.location, s"Inserted type must be the same as vector sub-type, got ${showType(subType)} and ${showType(index.typerep)}")]
     else []);
  
  local fwrd::Expr =
    ableC_Expr { inst insert_vector<$directTypeExpr{subType}>($Expr{lhs}, $Expr{index}, $Expr{elem}) };
  
  forwards to mkErrorCheck(localErrors, fwrd);
}

abstract production extendVector
top::Expr ::= e1::Expr e2::Expr
{
  top.pp = pp"${e1.pp}.extend(${e2.pp})";
  
  local subType::Type = vectorSubType(e1.typerep);
  local localErrors::[Message] =
    e1.errors ++ e2.errors ++
    checkVectorHeaderDef("extend_vector", top.location, top.env) ++
    checkVectorType(subType, e1.typerep, "extend", top.location) ++
    checkVectorType(subType, e2.typerep, "extend", top.location);
  
  local fwrd::Expr = ableC_Expr { inst extend_vector<$directTypeExpr{subType}>($Expr{e1}, $Expr{e2}) };
  
  forwards to mkErrorCheck(localErrors, fwrd);
}

abstract production memberVector
top::Expr ::= lhs::Expr deref::Boolean rhs::Name
{
  
  forwards to
    case rhs.name of
    | "size"      -> sizeVector(lhs, location=top.location)
    | "length"    -> sizeVector(lhs, location=top.location)
    | "capacity"  -> capacityVector(lhs, location=top.location)
    | n -> errorExpr([err(rhs.location, s"Vector does not have field ${n}")], location=top.location)
    end;
}

abstract production sizeVector
top::Expr ::= e::Expr
{
  top.pp = pp"${e.pp}.size";
  
  local subType::Type = vectorSubType(e.typerep);
  local fwrd::Expr =
    ableC_Expr {
      proto_typedef _vector_s;
      ((inst _vector_s<$directTypeExpr{subType}> *const)$Expr{e})->size
    };
  local localErrors::[Message] =
    e.errors ++
    checkVectorHeaderDef("_vector_s", top.location, top.env) ++
    checkVectorType(subType, e.typerep, "size", top.location);
  
  forwards to mkErrorCheck(localErrors, fwrd);
}

abstract production capacityVector
top::Expr ::= e::Expr
{
  top.pp = pp"${e.pp}.capacity";
  
  local subType::Type = vectorSubType(e.typerep);
  local fwrd::Expr =
    ableC_Expr {
      proto_typedef _vector_s;
      ((inst _vector_s<$directTypeExpr{subType}> *const)$Expr{e})->capacity
    };
  local localErrors::[Message] =
    e.errors ++
    checkVectorHeaderDef("_vector_s", top.location, top.env) ++
    checkVectorType(subType, e.typerep, "capacity", top.location);
  
  forwards to mkErrorCheck(localErrors, fwrd);
}

-- Check the given env for the given template name
function checkVectorHeaderDef
[Message] ::= n::String loc::Location env::Decorated Env
{
  return
    if !null(lookupTemplate(n, env))
    then []
    else [err(loc, "Missing include of vector.xh")];
}

-- Check that operand has vector type
function checkVectorType
[Message] ::= sub::Type t::Type op::String loc::Location
{
  return
    if typeAssignableTo(extType(nilQualifier(), vectorType(sub)), t)
    then []
    else [err(loc, s"Operand to ${op} expected vector<${showType(sub)}> (got ${showType(t)})")];
}

global builtin::Location = builtinLoc("vector");
