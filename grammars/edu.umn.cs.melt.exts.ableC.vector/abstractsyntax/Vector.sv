grammar edu:umn:cs:melt:exts:ableC:vector:abstractsyntax;

imports silver:langutil;
imports silver:langutil:pp;
imports silver:rewrite as s;

imports edu:umn:cs:melt:ableC:abstractsyntax:host hiding vectorType;
imports edu:umn:cs:melt:ableC:abstractsyntax:construction;
imports edu:umn:cs:melt:ableC:abstractsyntax:env;
--imports edu:umn:cs:melt:ableC:abstractsyntax:debug;

imports edu:umn:cs:melt:exts:ableC:templating;
imports edu:umn:cs:melt:exts:ableC:string;
imports edu:umn:cs:melt:exts:ableC:constructor;
imports edu:umn:cs:melt:exts:ableC:templateConstructor;
imports edu:umn:cs:melt:exts:ableC:allocation;

production currentArena
top::Expr ::= 
{
  top.pp = pp"current_arena";
  forwards to
    case top.env.allocContext of
    | arenaAllocContext(a) :: _ -> declRefExpr(^a)
    | _ -> errorExpr([errFromOrigin(top, "An arena allocator must be specified for vector creation")])
    end;
}

-- Vector initialization
abstract production newVector implements TemplateConstructor
top::Expr ::= targs::TemplateArgNames args::Exprs
{
  top.pp = pp"new vector<${ppImplode(pp", ", targs.pps)}>(${ppImplode(pp", ", args.pps)})";
  attachNote extensionGenerated("ableC-vector");
  
  targs.substEnv = s:fail();
  targs.paramNames = ["a"];
  targs.paramKinds = [nothing()];
  nondecorated local sub::Type =
    case targs.argreps of
    | consTemplateArg(typeTemplateArg(sub), nilTemplateArg()) -> ^sub
    | _ -> errorType()
    end;
  nondecorated local expectedSizeType::Type = builtinType(nilQualifier(), unsignedType(longType()));
  local localErrors::[Message] =
    checkVectorHeaderDef(top.env) ++
    case targs.argreps of
    | consTemplateArg(typeTemplateArg(sub), nilTemplateArg()) -> []
    | _ -> [errFromOrigin(top, "vector constructor expected a single type argument")]
    end ++
    case args of
    | consExpr(_, consExpr(_, consExpr(_, _))) ->
      [errFromOrigin(top, s"Too many arguments in vector expression")]
    | _ -> []
    end;

  nondecorated local size::Expr =
    case args of
    | consExpr(size, _) ->
      if typeAssignableTo(expectedSizeType, size.typerep)
      then size.bindRefExpr
      else errorExpr([errFromOrigin(size, s"Size must have type unsigned long (got ${show(80, size.typerep)})")])
    | _ -> ableC_Expr {0}
    end;
  nondecorated local init::Expr =
    case args of
    | consExpr(_, consExpr(init, _)) ->
      if typeAssignableTo(sub, init.typerep)
      then init.bindRefExpr
      else errorExpr([errFromOrigin(init, s"Initial value must have type ${show(80, sub)} (got ${show(80, init.typerep)})")])
    | _ -> ableC_Expr { ($directTypeExpr{sub})$Expr{defaultInitExpr(sub.host)} }
    end;
  nondecorated local fwrd::Expr =
    ableC_Expr { inst new_vector<$directTypeExpr{sub}>($Expr{size}, $Expr{init}, $Expr{currentArena()}) };
  
  forwards to bindTemplateConstructor(@targs, @args, mkErrorCheck(localErrors, fwrd));
}

aspect production emptyEnv
top::Env ::=
{
  globalTemplateConstructors <- [("vector", newVector)];
}

abstract production vectorInitializer implements ObjectInitializer
top::Initializer ::= i::InitList
{
  top.pp = ppConcat([text("{"), ppImplode(text(", "), i.pps), text("}")]);
  attachNote extensionGenerated("ableC-vector");
  
  i.vectorInitType =
    case top.expectedType of
    | extType(_, vectorType(sub)) -> ^sub
    | _ -> error("Vector initializer expected vector type")
    end;

  forwards to
    bindObjectInitializer(@i,
      warnExpr(
        i.vectorInitErrors,
        constructVector(
          typeName(directTypeExpr(i.vectorInitType), baseTypeExpr()),
          foldr(consVectorExpr, nilVectorExpr(), i.vectorInitExprs))));
}

inherited attribute vectorInitType::Type occurs on InitList, Init;
monoid attribute vectorInitExprs::[Expr] with [], ++ occurs on InitList, Init;
monoid attribute vectorInitErrors::[Message] with [], ++ occurs on InitList, Init;
propagate vectorInitType, vectorInitExprs, vectorInitErrors on InitList;

aspect production positionalInit
top::Init ::= i::Initializer
{
  attachNote extensionGenerated("ableC-vector");
  top.vectorInitExprs :=
    [ableC_Expr { ({$directTypeExpr{top.vectorInitType} _val = $Expr{top.bindRefExpr}; _val;}) }];
  top.vectorInitErrors := [];
}

aspect production designatedInit
top::Init ::= d::Designator i::Initializer
{
  top.vectorInitExprs := [];
  top.vectorInitErrors := [errFromOrigin(i, "Designated init not permitted in vector initializer")];
}

abstract production constructVector
top::Expr ::= sub::TypeName e::VectorExprs
{
  top.pp = pp"vec<${sub.pp}>[${ppImplode(pp", ", e.pps)}]";
  attachNote extensionGenerated("ableC-vector");
  
  local localErrors::[Message] =
    sub.errors ++ e.errors ++
    checkVectorHeaderDef(top.env);

  forward fwrd =
    ableC_Expr {
      inst from_array_vector<$TypeName{@sub}>(
        $Expr{mkIntConst(e.count)},
        $Expr{compoundLiteralExpr(
          typeName(sub.typerep.baseTypeExpr, sub.typerep.typeModifierExpr),
          @e.vectorInitTrans)},
        $Expr{currentArena()})
    };

  forwards to if null(localErrors) then @fwrd else errorExpr(localErrors);
}

abstract production inferredConstructVector
top::Expr ::= e::VectorExprs
{
  top.pp = pp"vec[${ppImplode(pp", ", e.pps)}]";
  attachNote extensionGenerated("ableC-vector");
  
  local localErrors::[Message] =
    e.errors ++
    (if e.count == 0
     then [errFromOrigin(top, "Can't infer type argument for empty vector")]
     else []) ++
    checkVectorHeaderDef(top.env);

  nondecorated local arena::Expr =
    case top.env.allocContext of
    | arenaAllocContext(a) :: _ -> declRefExpr(^a)
    | _ -> errorExpr([errFromOrigin(top, "An arena allocator must be specified for vector construction")])
    end;

  forward fwrd =
    ableC_Expr {
      inst from_array_vector<$directTypeExpr{e.typerep}>(
        $Expr{mkIntConst(e.count)},
        $Expr{compoundLiteralExpr(
          typeName(e.typerep.baseTypeExpr, e.typerep.typeModifierExpr),
          @e.vectorInitTrans)},
        $Expr{arena})
    };
  
  forwards to if null(localErrors) then @fwrd else errorExpr(localErrors);
}

nonterminal VectorExprs with pps, count, errors, typerep, vectorInitTrans;
translation attribute vectorInitTrans::InitList;

propagate errors on VectorExprs;

abstract production consVectorExpr
top::VectorExprs ::= h::Expr t::VectorExprs
{
  attachNote extensionGenerated("ableC-vector");
  top.pps = h.pp :: t.pps;
  top.count = 1 + t.count;
  top.typerep = h.typerep;
  top.vectorInitTrans = consInit(positionalInit(exprInitializer(@h)), @t.vectorInitTrans);
  --h.env = top.vectorInitTrans.env; -- TODO: Should this equation be needed?
}

abstract production nilVectorExpr
top::VectorExprs ::=
{
  attachNote extensionGenerated("ableC-vector");
  top.pps = [];
  top.count = 0;
  top.typerep = errorType();
  top.vectorInitTrans = nilInit();
}

abstract production concatVector implements BinaryOp
top::Expr ::= @e1::Expr @e2::Expr
{
  top.pp = pp"${e1.pp} + ${e2.pp}";
  attachNote extensionGenerated("ableC-vector");
  
  nondecorated local subType::Type = vectorSubType(e1.typerep);
  local localErrors::[Message] =
    checkVectorHeaderDef(top.env) ++
    checkVectorType(subType, e1, "concat") ++
    checkVectorType(subType, e2, "concat");

  nondecorated local fwrd::Expr = ableC_Expr {
    inst extend_vector<$directTypeExpr{subType}>(
      inst copy_vector<$directTypeExpr{subType}>($Expr{e1.bindRefExpr}),
      $Expr{e2.bindRefExpr})
  };
  
  forwards to bindBinaryOp(e1, e2, mkErrorCheck(localErrors, fwrd));
}

abstract production equalsVector implements BinaryOp
top::Expr ::= @e1::Expr @e2::Expr
{
  top.pp = pp"${e1.pp} == ${e2.pp}";
  attachNote extensionGenerated("ableC-vector");
  
  nondecorated local subType::Type = vectorSubType(e1.typerep);
  local localErrors::[Message] =
    checkVectorHeaderDef(top.env) ++
    checkVectorType(subType, e1, "==") ++
    checkVectorType(subType, e2, "==");
    -- TODO: Check that == is defined for subType
  nondecorated local fwrd::Expr = ableC_Expr {
    inst equals_vector<$directTypeExpr{subType}>(
      $Expr{e1.bindRefExpr}, $Expr{e2.bindRefExpr})
  };
  
  forwards to bindBinaryOp(e1, e2, mkErrorCheck(localErrors, fwrd));
}

abstract production subscriptVector implements BinaryOp
top::Expr ::= @e1::Expr @e2::Expr
{
  top.pp = pp"${e1.pp}[${e2.pp}]";
  attachNote extensionGenerated("ableC-vector");
  
  nondecorated local subType::Type = vectorSubType(e1.typerep);
  local localErrors::[Message] =
    checkVectorHeaderDef(top.env) ++
    checkVectorType(subType, e1, "[]") ++
    if e2.typerep.isIntegerType
    then []
    else [errFromOrigin(e2, s"Vector index must have integer type, but got ${show(80, e2.typerep)}")];

  nondecorated local fwrd::Expr =
    ableC_Expr {
      proto_typedef _vector_s;
      ((inst _vector_s<$directTypeExpr{subType}> *const)$Expr{e1.bindRefExpr})->contents[
        inst _check_index_vector<$directTypeExpr{subType}>($Expr{e1.bindRefExpr}, $Expr{e2.bindRefExpr})]
    };
  
  forwards to bindBinaryOp(e1, e2, mkErrorCheck(localErrors, fwrd));
}

abstract production callMemberVector implements MemberCall
top::Expr ::= @lhs::Expr deref::Boolean rhs::Name a::Exprs
{
  top.pp = forwardParent.pp;
  
  forwards to bindMemberCall(lhs, deref, @rhs, @a,
    case rhs.name, a.bindRefExprs of
    | "append", [e] -> appendVector(lhs.bindRefExpr, e)
    | "insert", [e1, e2] -> insertVector(lhs.bindRefExpr, e1, e2)
    | "extend", [e] -> extendVector(lhs.bindRefExpr, e)
    | "copy", [] -> copyVector(lhs.bindRefExpr)
    | "pop", [] -> popVector(lhs.bindRefExpr)
    | n, _ -> errorExpr([errFromOrigin(rhs, s"Vector does not have field ${n} with ${toString(a.count)} parameters")])
    end);
}

abstract production copyVector
top::Expr ::= e::Expr
{
  top.pp = pp"${e.pp}.copy()";
  attachNote extensionGenerated("ableC-vector");
  
  nondecorated local subType::Type = vectorSubType(e.typerep);
  local localErrors::[Message] =
    checkVectorHeaderDef(top.env) ++
    checkVectorType(subType, e, "vector copy");
  forward fwrd =
    ableC_Expr { inst copy_vector<$directTypeExpr{subType}>($Expr{@e}) };

  forwards to if null(localErrors) then @fwrd else errorExpr(localErrors);
}

abstract production popVector
top::Expr ::= e::Expr
{
  top.pp = pp"${e.pp}.pop()";
  attachNote extensionGenerated("ableC-vector");
  
  nondecorated local subType::Type = vectorSubType(e.typerep);
  local localErrors::[Message] =
    e.errors ++
    checkVectorHeaderDef(top.env) ++
    checkVectorType(subType, e, "vector pop");
  forward fwrd =
    ableC_Expr { inst pop_vector<$directTypeExpr{subType}>($Expr{@e}) };

  forwards to if null(localErrors) then @fwrd else errorExpr(localErrors);
}

abstract production appendVector
top::Expr ::= lhs::Expr elem::Expr
{
  top.pp = pp"${lhs.pp}.append(${elem.pp})";
  attachNote extensionGenerated("ableC-vector");
  
  nondecorated local subType::Type = vectorSubType(lhs.typerep);
  local localErrors::[Message] =
    lhs.errors ++ elem.errors ++
    checkVectorHeaderDef(top.env) ++
    checkVectorType(subType, lhs, "append") ++
    if !typeAssignableTo(subType, elem.typerep)
    then [errFromOrigin(top, s"Appended type must be the same as vector sub-type, got ${show(80, subType)} and ${show(80, elem.typerep)}")]
    else [];
  
  forward fwrd =
    ableC_Expr { inst append_vector<$directTypeExpr{subType}>($Expr{@lhs}, $Expr{@elem}) };

  forwards to if null(localErrors) then @fwrd else errorExpr(localErrors);
}

abstract production insertVector
top::Expr ::= lhs::Expr index::Expr elem::Expr
{
  top.pp = pp"${lhs.pp}.insert(${index.pp}, ${elem.pp})";
  attachNote extensionGenerated("ableC-vector");
  
  nondecorated local subType::Type = vectorSubType(lhs.typerep);
  local localErrors::[Message] =
    lhs.errors ++ index.errors ++ elem.errors ++
    checkVectorHeaderDef(top.env) ++
    checkVectorType(subType, lhs, "insert") ++
    (if index.typerep.isIntegerType
     then []
     else [errFromOrigin(index, s"Vector insertion index must have integer type, but got ${show(80, index.typerep)}")]) ++
    (if !typeAssignableTo(subType, elem.typerep)
     then [errFromOrigin(top, s"Inserted type must be the same as vector sub-type, got ${show(80, subType)} and ${show(80, index.typerep)}")]
     else []);
  
  forward fwrd =
    ableC_Expr { inst insert_vector<$directTypeExpr{subType}>($Expr{@lhs}, $Expr{@index}, $Expr{@elem}) };

  forwards to if null(localErrors) then @fwrd else errorExpr(localErrors);
}

abstract production extendVector
top::Expr ::= e1::Expr e2::Expr
{
  top.pp = pp"${e1.pp}.extend(${e2.pp})";
  attachNote extensionGenerated("ableC-vector");
  
  nondecorated local subType::Type = vectorSubType(e1.typerep);
  local localErrors::[Message] =
    e1.errors ++ e2.errors ++
    checkVectorHeaderDef(top.env) ++
    checkVectorType(subType, e1, "extend") ++
    checkVectorType(subType, e2, "extend");
  
  forward fwrd =
    ableC_Expr { inst extend_vector<$directTypeExpr{subType}>($Expr{@e1}, $Expr{@e2}) };

  forwards to if null(localErrors) then @fwrd else errorExpr(localErrors);
}

abstract production memberVector implements MemberAccess
top::Expr ::= @lhs::Expr deref::Boolean rhs::Name
{
  top.pp = forwardParent.pp;
  forwards to bindMemberAccess(lhs, deref, @rhs,
    case rhs.name of
    | "size"      -> sizeVector(lhs.bindRefExpr)
    | "length"    -> sizeVector(lhs.bindRefExpr)
    | "capacity"  -> capacityVector(lhs.bindRefExpr)
    | n -> errorExpr([errFromOrigin(rhs, s"Vector does not have field ${n}")])
    end);
}

abstract production sizeVector
top::Expr ::= e::Expr
{
  top.pp = pp"${e.pp}.size";
  attachNote extensionGenerated("ableC-vector");
  
  nondecorated local subType::Type = vectorSubType(e.typerep);
  local localErrors::[Message] =
    e.errors ++
    checkVectorHeaderDef(top.env) ++
    checkVectorType(subType, e, "size");

  forward fwrd =
    ableC_Expr {
      proto_typedef _vector_s;
      ((inst _vector_s<$directTypeExpr{subType}> *const)$Expr{@e})->size
    };

  forwards to if null(localErrors) then @fwrd else errorExpr(localErrors);
}

abstract production capacityVector
top::Expr ::= e::Expr
{
  top.pp = pp"${e.pp}.capacity";
  attachNote extensionGenerated("ableC-vector");
  
  nondecorated local subType::Type = vectorSubType(e.typerep);
  local localErrors::[Message] =
    e.errors ++
    checkVectorHeaderDef(top.env) ++
    checkVectorType(subType, e, "capacity");

  forward fwrd =
    ableC_Expr {
      proto_typedef _vector_s;
      ((inst _vector_s<$directTypeExpr{subType}> *const)$Expr{@e})->capacity
    };

  forwards to if null(localErrors) then @fwrd else errorExpr(localErrors);
}

-- Check the given env for the given template name
fun checkVectorHeaderDef [Message] ::= env::Env =
  if !null(lookupTemplate("_vector_s", env))
  then []
  else [errFromOrigin(ambientOrigin(), "Missing include of vector.xh")];

-- Check that operand has vector type
fun checkVectorType
[Message] ::= sub::Type e::Decorated Expr op::String =
  if typeAssignableTo(extType(nilQualifier(), vectorType(sub)), e.typerep)
  then []
  else [errFromOrigin(e, s"Operand to ${op} expected vector<${show(80, sub)}> (got ${show(80, e.typerep)})")];
