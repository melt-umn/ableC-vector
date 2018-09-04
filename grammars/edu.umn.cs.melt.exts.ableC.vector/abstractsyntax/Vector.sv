grammar edu:umn:cs:melt:exts:ableC:vector:abstractsyntax;

imports silver:langutil;
imports silver:langutil:pp;

imports edu:umn:cs:melt:ableC:abstractsyntax:host hiding vectorType;
imports edu:umn:cs:melt:ableC:abstractsyntax:construction;
imports edu:umn:cs:melt:ableC:abstractsyntax:env;
imports edu:umn:cs:melt:ableC:abstractsyntax:substitution;
imports edu:umn:cs:melt:ableC:abstractsyntax:overloadable as ovrld;
--imports edu:umn:cs:melt:ableC:abstractsyntax:debug;

imports edu:umn:cs:melt:exts:ableC:templating;
imports edu:umn:cs:melt:exts:ableC:string;

-- Vector initialization
abstract production newVector
top::Expr ::= sub::TypeName size::Expr
{
  propagate substituted;
  top.pp = pp"vec<${sub.pp}>(${size.pp})";
  
  local localErrors::[Message] =
    sub.errors ++ checkVectorHeaderDef("new_vector", top.location, top.env);
  
  sub.env = globalEnv(top.env);
  
  local fwrd::Expr = ableC_Expr { inst new_vector<$TypeName{sub}>($Expr{size}) };
  
  forwards to mkErrorCheck(localErrors, fwrd);
}

abstract production constructVector
top::Expr ::= sub::TypeName e::Exprs
{
  propagate substituted;
  top.pp = pp"vec<${sub.pp}> [${ppImplode(pp", ", e.pps)}]";
  
  local localErrors::[Message] =
    sub.errors ++ e.vectorInitErrors ++
    checkVectorHeaderDef("new_vector", top.location, top.env);
  
  sub.env = globalEnv(top.env);
  
  e.argumentPosition = 0;
  e.vectorInitType = sub.typerep;
  
  local fwrd::Expr =
    ableC_Expr {
      ({$BaseTypeExpr{vectorTypeExpr(nilQualifier(), sub, builtin)} _vec =
          $Expr{
            newVector(
              typeName(directTypeExpr(sub.typerep), baseTypeExpr()),
              mkIntConst(e.count, builtin),
              location=builtin)};
        $Stmt{e.vectorInitTrans}
        _vec;})
    };
  
  forwards to mkErrorCheck(localErrors, fwrd);
}

autocopy attribute vectorInitType::Type occurs on Exprs;

synthesized attribute vectorInitErrors::[Message] occurs on Exprs;
synthesized attribute vectorInitTrans::Stmt occurs on Exprs;

aspect production consExpr
top::Exprs ::= h::Expr t::Exprs
{
  top.vectorInitErrors =
    (if !typeAssignableTo(h.typerep, top.vectorInitType)
     then [err(h.location, s"Invalid type to vector initializer: Expected ${showType(top.vectorInitType)}, got ${showType(h.typerep)}")]
     else []) ++ t.vectorInitErrors;
  top.vectorInitTrans =
    ableC_Stmt {
      _vec[$intLiteralExpr{top.argumentPosition}] = $Expr{h};
      $Stmt{t.vectorInitTrans}
    };
}

aspect production nilExpr
top::Exprs ::= 
{
  top.vectorInitErrors = [];
  top.vectorInitTrans = nullStmt();
}

abstract production concatVector
top::Expr ::= e1::Expr e2::Expr
{
  propagate substituted;
  top.pp = pp"${e1.pp} + ${e2.pp}";
  
  local subType::Type = vectorSubType(e1.typerep);
  local localErrors::[Message] =
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
  propagate substituted;
  top.pp = pp"${e1.pp} == ${e2.pp}";
  
  local subType::Type = vectorSubType(e1.typerep);
  local localErrors::[Message] =
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
  propagate substituted;
  top.pp = pp"${e1.pp}[${e2.pp}]";
  
  local subType::Type = vectorSubType(e1.typerep);
  local localErrors::[Message] =
    checkVectorHeaderDef("_check_index_vector", top.location, top.env) ++
    checkVectorType(subType, e1.typerep, "[]", top.location) ++
    if e2.typerep.isIntegerType
    then []
    else [err(e2.location, s"Vector index must have integer type, but got ${showType(e2.typerep)}")];
  
  local vecTempName::String = "_vec_" ++ toString(genInt());
  local indexTempName::String = "_index_" ++ toString(genInt());
  local fwrd::Expr =
    ableC_Expr {
      ({$directTypeExpr{e1.typerep} $name{vecTempName} = $Expr{e1};
        $directTypeExpr{e2.typerep} $name{indexTempName} = $Expr{e2};
        inst _check_index_vector<$directTypeExpr{subType}>($name{vecTempName}, $name{indexTempName});
        (($directTypeExpr{e1.typerep.host})$name{vecTempName})->contents + $name{indexTempName};})
    };
  
  forwards to mkErrorCheck(localErrors, fwrd);
}

abstract production callMemberVector
top::Expr ::= lhs::Expr deref::Boolean rhs::Name a::Exprs
{
  propagate substituted;
  
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
  propagate substituted;
  top.pp = pp"${e.pp}.copy()";
  
  local subType::Type = vectorSubType(e.typerep);
  local localErrors::[Message] =
    checkVectorHeaderDef("copy_vector", top.location, top.env) ++
    checkVectorType(subType, e.typerep, "vector copy", top.location);
  local fwrd::Expr = ableC_Expr { inst copy_vector<$directTypeExpr{subType}>($Expr{e}) };
  
  forwards to mkErrorCheck(localErrors, fwrd);
}

abstract production appendVector
top::Expr ::= lhs::Expr elem::Expr
{
  propagate substituted;
  top.pp = pp"${lhs.pp}.append(${elem.pp})";
  
  local subType::Type = vectorSubType(lhs.typerep);
  local localErrors::[Message] =
    checkVectorHeaderDef("append_vector", top.location, top.env) ++
    checkVectorType(subType, lhs.typerep, "append", top.location) ++
    if !compatibleTypes(subType, elem.typerep, true, false)
    then [err(top.location, s"Appended type must be the same as vector sub-type, got ${showType(subType)} and ${showType(elem.typerep)}")]
    else [];
  
  local fwrd::Expr = ableC_Expr { inst append_vector<$directTypeExpr{subType}>($Expr{lhs}, $Expr{elem}) };
  
  forwards to mkErrorCheck(localErrors, fwrd);
}

abstract production insertVector
top::Expr ::= lhs::Expr index::Expr elem::Expr
{
  propagate substituted;
  top.pp = pp"${lhs.pp}.insert(${index.pp}, ${elem.pp})";
  
  local subType::Type = vectorSubType(lhs.typerep);
  local localErrors::[Message] =
    checkVectorHeaderDef("insert_vector", top.location, top.env) ++
    checkVectorType(subType, lhs.typerep, "insert", top.location) ++
    (if index.typerep.isIntegerType
     then []
     else [err(index.location, s"Vector insertion index must have integer type, but got ${showType(index.typerep)}")]) ++
    (if !compatibleTypes(subType, index.typerep, true, false)
     then [err(top.location, s"Inserted type must be the same as vector sub-type, got ${showType(subType)} and ${showType(index.typerep)}")]
     else []);
  
  local fwrd::Expr =
    ableC_Expr { inst insert_vector<$directTypeExpr{subType}>($Expr{lhs}, $Expr{index}, $Expr{elem}) };
  
  forwards to mkErrorCheck(localErrors, fwrd);
}

abstract production extendVector
top::Expr ::= e1::Expr e2::Expr
{
  propagate substituted;
  top.pp = pp"${e1.pp}.extend(${e2.pp})";
  
  local subType::Type = vectorSubType(e1.typerep);
  local localErrors::[Message] =
    checkVectorHeaderDef("extend_vector", top.location, top.env) ++
    checkVectorType(subType, e1.typerep, "extend", top.location) ++
    checkVectorType(subType, e2.typerep, "extend", top.location);
  
  local fwrd::Expr = ableC_Expr { inst extend_vector<$directTypeExpr{subType}>($Expr{e1}, $Expr{e2}) };
  
  forwards to mkErrorCheck(localErrors, fwrd);
}

abstract production memberVector
top::Expr ::= lhs::Expr deref::Boolean rhs::Name
{
  propagate substituted;
  
  forwards to
    case rhs.name of
      "length"    -> lengthVector(lhs, location=top.location)
    | "size"      -> lengthVector(lhs, location=top.location)
    | "capacity"  -> capacityVector(lhs, location=top.location)
    | n -> errorExpr([err(rhs.location, s"Vector does not have field ${n}")], location=top.location)
    end;
}

abstract production lengthVector
top::Expr ::= e::Expr
{
  propagate substituted;
  top.pp = pp"${e.pp}.length";
  
  local subType::Type = vectorSubType(e.typerep);
  local fwrd::Expr = ableC_Expr { ((const $directTypeExpr{e.typerep.host})$Expr{e})->length };
  local localErrors::[Message] =
    checkVectorHeaderDef("_vector_s", top.location, top.env) ++
    checkVectorType(subType, e.typerep, "length", top.location);
  
  forwards to mkErrorCheck(localErrors, fwrd);
}

abstract production capacityVector
top::Expr ::= e::Expr
{
  propagate substituted;
  top.pp = pp"${e.pp}.capacity";
  
  local subType::Type = vectorSubType(e.typerep);
  local fwrd::Expr = ableC_Expr { ((const $directTypeExpr{e.typerep.host})$Expr{e})->capacity };
  local localErrors::[Message] =
    checkVectorHeaderDef("_vector_s", top.location, top.env) ++
    checkVectorType(subType, e.typerep, "capacity", top.location);
  
  forwards to mkErrorCheck(localErrors, fwrd);
}

abstract production showVector
top::Expr ::= e::Expr
{
  propagate substituted;
  top.pp = pp"show(${e.pp})";
  
  local subType::Type = vectorSubType(e.typerep);
  local localErrors::[Message] =
    checkVectorHeaderDef("show_vector", top.location, top.env) ++
    checkVectorType(subType, e.typerep, "show", top.location) ++
    case subType.showProd of
      just(p) -> []
    | nothing() -> [err(e.location, s"show of ${showType(e.typerep)} is not defined, because show of ${showType(subType)} is not defined")]
    end;
  
  local fwrd::Expr = ableC_Expr { inst show_vector<$directTypeExpr{subType}>($Expr{e}) };
  
  forwards to mkErrorCheck(localErrors, fwrd);
}

-- Check the given env for the given function name
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
