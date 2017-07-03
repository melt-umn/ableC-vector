grammar edu:umn:cs:melt:exts:ableC:vector:abstractsyntax;

imports silver:langutil;
imports silver:langutil:pp;

imports edu:umn:cs:melt:ableC:abstractsyntax hiding vectorType;
imports edu:umn:cs:melt:ableC:abstractsyntax:construction;
imports edu:umn:cs:melt:ableC:abstractsyntax:construction:parsing;
imports edu:umn:cs:melt:ableC:abstractsyntax:env;
imports edu:umn:cs:melt:ableC:abstractsyntax:substitution;
imports edu:umn:cs:melt:ableC:abstractsyntax:overload as ovrld;
--imports edu:umn:cs:melt:ableC:abstractsyntax:debug;

imports edu:umn:cs:melt:exts:ableC:templating;
imports edu:umn:cs:melt:exts:ableC:string;

global builtin::Location = builtinLoc("vector");

aspect function ovrld:getAddOpOverload
Maybe<(Expr ::= Expr Expr Location)> ::= l::Type r::Type env::Decorated Env
{
  overloads <-
    [pair(
       pair(
         "edu:umn:cs:melt:exts:ableC:vector:vector",
         "edu:umn:cs:melt:exts:ableC:vector:vector"),
       concatVector(_, _, location=_))];
}

aspect function ovrld:getSubscriptAssignOverload
Maybe<(Expr ::= Expr Expr AssignOp Expr Location)> ::= t::Type env::Decorated Env
{
  overloads <-
    [pair(
       "edu:umn:cs:melt:exts:ableC:vector:vector",
       subscriptAssignVector(_, _, _, _, location=_))];
}

aspect function ovrld:getMemberAssignOverload
Maybe<(Expr ::= Expr Boolean Name AssignOp Expr Location)> ::= t::Type env::Decorated Env
{
  overloads <-
    [pair(
       "edu:umn:cs:melt:exts:ableC:vector:vector",
       memberAssignVector(_, _, _, _, _, location=_))];
}

aspect function ovrld:getEqualsOpOverload
Maybe<(Expr ::= Expr Expr Location)> ::= l::Type r::Type env::Decorated Env
{
  overloads <-
    [pair(
       pair(
         "edu:umn:cs:melt:exts:ableC:vector:vector",
         "edu:umn:cs:melt:exts:ableC:vector:vector"),
       eqVector(_, _, location=_))];
}

aspect function ovrld:getArraySubscriptOverload
Maybe<(Expr ::= Expr Expr Location)> ::= t::Type env::Decorated Env
{
  overloads <-
    [pair("edu:umn:cs:melt:exts:ableC:vector:vector", subscriptVector(_, _, location=_))];
}

aspect function ovrld:getMemberOverload
Maybe<(Expr ::= Expr Boolean Name Location)> ::= t::Type env::Decorated Env
{
  overloads <-
    [pair("edu:umn:cs:melt:exts:ableC:vector:vector", memberVector(_, _, _, location=_))];
}

aspect function ovrld:getMemberCallOverload
Maybe<(Expr ::= Expr Boolean Name Exprs Location)> ::= t::Type env::Decorated Env
{
  overloads <-
    [pair(
       "edu:umn:cs:melt:exts:ableC:vector:vector",
       memberCallVector(_, _, _, _, location=_))];
}

aspect function getShowOverload
Maybe<(Expr ::= Expr Location)> ::= t::Type env::Decorated Env
{
  overloads <- [pair("edu:umn:cs:melt:exts:ableC:vector:vector", showVector(_, location=_))];
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
    | "elem_size" -> elemSizeVector(lhs, location=top.location)
    -- Needed for built-in functions
    | "_info" -> memberExpr(lhs, deref, rhs, location=top.location)
    | "_contents" -> memberExpr(lhs, deref, rhs, location=top.location)
    
    | n -> errorExpr([err(rhs.location, s"Vector does not have field ${n}")], location=top.location)
    end;
}

abstract production memberAssignVector
top::Expr ::= lhs::Expr deref::Boolean rhs::Name op::AssignOp val::Expr
{
  propagate substituted;
  
  forwards to
    case rhs.name of
    | n -> errorExpr([err(rhs.location, s"Cannot assign to field ${n} of vector")], location=top.location)
    end;
}

abstract production memberCallVector
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

-- Vector initialization
abstract production newVector
top::Expr ::= sub::TypeName size::Expr
{
  propagate substituted;
  top.pp = pp"vec<${sub.pp}>(${size.pp})";
  
  local localErrors::[Message] =
    sub.errors ++ checkVectorHeaderDef("_new_vector", top.location, top.env);
  
  sub.env = globalEnv(top.env);
  
  local fwrd::Expr =
    callExpr(
      templateDeclRefExpr(
        name("_new_vector", location=builtin),
        consTypeName(sub, nilTypeName()),
        location=builtin),
      consExpr(size, nilExpr()),
      location=builtin);
  
  forwards to mkErrorCheck(localErrors, fwrd);
}

global constructVectorFwrd::Expr = parseExpr(s"""
({proto_typedef __vector_type__;
  __vector_type__ _vec = __new_vec__;
  __init__;
  _vec;})""");

abstract production constructVector
top::Expr ::= sub::TypeName e::Exprs
{
  propagate substituted;
  top.pp = pp"vec<${sub.pp}> [${ppImplode(pp", ", e.pps)}]";
  
  local localErrors::[Message] =
    sub.errors ++ e.vectorInitErrors ++
    checkVectorHeaderDef("_new_vector", top.location, top.env);
  
  sub.env = globalEnv(top.env);
  
  e.argumentPosition = 0;
  e.vectorInitType = sub.typerep;
  
  local fwrd::Expr =
    subExpr(
      [typedefSubstitution("__vector_type__", vectorTypeExpr(nilQualifier(), sub)),
       declRefSubstitution(
         "__new_vec__",
         newVector(
           typeName(directTypeExpr(sub.typerep), baseTypeExpr()),
           mkIntConst(e.count, builtin),
           location=builtin)),
       stmtSubstitution("__init__", e.vectorInitTrans)],
      constructVectorFwrd);
  
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
    seqStmt(
      exprStmt(
        subscriptAssignVector(
          declRefExpr(name("_vec", location=builtin), location=builtin),
          mkIntConst(top.argumentPosition, builtin),
          eqOp(location=builtin),
          h,
          location=builtin)),
      t.vectorInitTrans);
}

aspect production nilExpr
top::Exprs ::= 
{
  top.vectorInitErrors = [];
  top.vectorInitTrans = nullStmt();
}

abstract production copyVector
top::Expr ::= e::Expr
{
  propagate substituted;
  top.pp = pp"copy_vector(${e.pp})";
  
  local subType::Type = vectorSubType(e.typerep, top.env);
  
  local localErrors::[Message] =
    checkVectorHeaderDef("_copy_vector", top.location, top.env) ++
    if !isVectorType(e.typerep, top.env)
    then [err(e.location, s"Vector copy expected vector type, got ${showType(e.typerep)}")]
    else [];
  local fwrd::Expr =
    callExpr(
      templateDeclRefExpr(
        name("_copy_vector", location=builtin),
        consTypeName(typeName(directTypeExpr(subType), baseTypeExpr()), nilTypeName()),
        location=builtin),
      consExpr(e, nilExpr()),
      location=builtin);
  
  forwards to mkErrorCheck(localErrors, fwrd);
}

abstract production concatVector
top::Expr ::= e1::Expr e2::Expr
{
  propagate substituted;
  top.pp = pp"${e1.pp} + ${e2.pp}";
  
  local subType::Type = vectorSubType(e1.typerep, top.env);
  local vecTempName::String = "_vec_" ++ toString(genInt());
  
  forwards to 
    stmtExpr(
      foldStmt([
        mkDecl(vecTempName, vectorType(nilQualifier(), subType), copyVector(e1, location=builtin), builtin),
        exprStmt(
          extendVector(
            declRefExpr(name(vecTempName, location=builtin), location=builtin),
            e2,
            location=builtin))]),
      declRefExpr(name(vecTempName, location=builtin), location=builtin),
      location=builtin);
}

abstract production eqVector
top::Expr ::= e1::Expr e2::Expr
{
  propagate substituted;
  top.pp = pp"${e1.pp} == ${e2.pp}";
  
  local subType::Type = vectorSubType(e1.typerep, top.env);
  local funName::String = "_eq_vector_" ++ subType.mangledName;
  
  local localErrors::[Message] =
    checkVectorHeaderDef("_eq_vector", top.location, top.env) ++
    if !compatibleTypes(subType, vectorSubType(e2.typerep, top.env), true, false)
    then [err(top.location, s"Vector equality sub-types must be the same, got ${showType(e1.typerep)} and ${showType(e2.typerep)}")]
    else [];
  local fwrd::Expr =
    callExpr(
      templateDeclRefExpr(
        name("_eq_vector", location=builtin),
        consTypeName(typeName(directTypeExpr(subType), baseTypeExpr()), nilTypeName()),
        location=builtin),
      consExpr(e1, consExpr(e2, nilExpr())),
      location=builtin);
  
  forwards to mkErrorCheck(localErrors, fwrd);
}

abstract production lengthVector
top::Expr ::= e::Expr
{
  propagate substituted;
  top.pp = pp"${e.pp}.length";
  
  local subType::Type = vectorSubType(e.typerep, top.env);
  local fwrd::Expr =
    memberExpr(
      memberExpr(e, false, name("_info", location=builtin), location=builtin),
      true,
      name("length", location=builtin),
      location=builtin);
  
  forwards to mkErrorCheck(checkVectorHeaderDef("_vector_s", top.location, top.env), fwrd);
}

abstract production capacityVector
top::Expr ::= e::Expr
{
  propagate substituted;
  top.pp = pp"${e.pp}.capacity";

  local subType::Type = vectorSubType(e.typerep, top.env);
  local fwrd::Expr =
    memberExpr(
      memberExpr(e, false, name("_info", location=builtin), location=builtin),
      true,
      name("capacity", location=builtin),
      location=builtin);
  
  forwards to mkErrorCheck(checkVectorHeaderDef("_vector_s", top.location, top.env), fwrd);
}

abstract production elemSizeVector
top::Expr ::= e::Expr
{
  propagate substituted;
  top.pp = pp"${e.pp}.elem_size";
  
  local subType::Type = vectorSubType(e.typerep, top.env);
  local fwrd::Expr =
    memberExpr(
      memberExpr(e, false, name("_info", location=builtin), location=builtin),
      true,
      name("elem_size", location=builtin),
      location=builtin);
  
  forwards to mkErrorCheck(checkVectorHeaderDef("_vector_s", top.location, top.env), fwrd);
}

abstract production subscriptVector
top::Expr ::= e1::Expr e2::Expr
{
  propagate substituted;
  top.pp = pp"${e1.pp}[${e2.pp}]";
  
  local subType::Type = vectorSubType(e1.typerep, top.env);
  local vecTempName::String = "_vec_" ++ toString(genInt());
  local indexTempName::String = "_index_" ++ toString(genInt());

  local localErrors::[Message] =
    checkVectorHeaderDef("_check_index_vector", top.location, top.env) ++
    if e2.typerep.isIntegerType
    then []
    else [err(e2.location, s"Vector index must have integer type, but got ${showType(e2.typerep)}")];
  local fwrd::Expr =
    stmtExpr(
      foldStmt([
        mkDecl(vecTempName, e1.typerep, e1, builtin),
        mkDecl(indexTempName, e2.typerep, e2, builtin),
        exprStmt(
          callExpr(
            templateDeclRefExpr(
              name("_check_index_vector", location=builtin),
              consTypeName(typeName(directTypeExpr(subType), baseTypeExpr()), nilTypeName()),
              location=builtin),
            consExpr(
              declRefExpr(name(vecTempName, location=builtin), location=builtin),
              consExpr(
                declRefExpr(name(indexTempName, location=builtin), location=builtin),
                nilExpr())),
            location=builtin))]),
        arraySubscriptExpr(
          unaryOpExpr(
            dereferenceOp(location=builtin),
            memberExpr(
              declRefExpr(name(vecTempName, location=builtin), location=builtin),
              false,
              name("_contents", location=builtin),
              location=builtin),
            location=builtin),
          declRefExpr(name(indexTempName, location=builtin), location=builtin), location=builtin),
        location=builtin);
  
  forwards to mkErrorCheck(localErrors, fwrd);
}

abstract production subscriptAssignVector
top::Expr ::= lhs::Expr index::Expr op::AssignOp rhs::Expr
{
  propagate substituted;
  top.pp = pp"${lhs.pp}[${index.pp}] ${op.pp} ${rhs.pp}";
  
  local subType::Type = vectorSubType(lhs.typerep, top.env);
  local vecTempName::String = "_vec_" ++ toString(genInt());
  local indexTempName::String = "_index_" ++ toString(genInt());

  local localErrors::[Message] =
    checkVectorHeaderDef("_check_index_vector", top.location, top.env) ++
    (if index.typerep.isIntegerType
     then []
     else [err(index.location, s"Vector index must have integer type, but got ${showType(index.typerep)}")]) ++
    (if !typeAssignableTo(subType, rhs.typerep)
     then [err(top.location, s"Vector index assign sub-type and rhs type must be the same, got ${showType(subType)} and ${showType(rhs.typerep)}")]
     else []);
  local fwrd::Expr =
    stmtExpr(
      foldStmt([
        mkDecl(vecTempName, lhs.typerep, lhs, builtin),
        mkDecl(indexTempName, index.typerep, index, builtin),
        exprStmt(
          callExpr(
            templateDeclRefExpr(
              name("_check_index_vector", location=builtin),
              consTypeName(typeName(directTypeExpr(subType), baseTypeExpr()), nilTypeName()),
              location=builtin),
            consExpr(
              declRefExpr(name(vecTempName, location=builtin), location=builtin),
              consExpr(
                declRefExpr(name(indexTempName, location=builtin), location=builtin),
                nilExpr())),
            location=builtin))]),
        binaryOpExpr(
          arraySubscriptExpr(
            unaryOpExpr(
              dereferenceOp(location=builtin),
              memberExpr(
                declRefExpr(name(vecTempName, location=builtin), location=builtin),
                false,
                name("_contents", location=builtin),
                location=builtin),
              location=builtin),
            declRefExpr(name(indexTempName, location=builtin), location=builtin), location=builtin),
          assignOp(op, location=builtin),
          rhs,
          location=builtin),
        location=builtin);
  
  forwards to mkErrorCheck(localErrors, fwrd);
}

abstract production appendVector
top::Expr ::= lhs::Expr elem::Expr
{
  propagate substituted;
  top.pp = pp"${lhs.pp}.append(${elem.pp})";
  
  local subType::Type = vectorSubType(lhs.typerep, top.env);
  
  local localErrors::[Message] =
    checkVectorHeaderDef("_append_vector", top.location, top.env) ++
    if !compatibleTypes(subType, elem.typerep, true, false)
    then [err(top.location, s"Appended type must be the same as vector sub-type, got ${showType(subType)} and ${showType(elem.typerep)}")]
    else [];

  local fwrd::Expr =
    callExpr(
      templateDeclRefExpr(
        name("_append_vector", location=builtin),
        consTypeName(typeName(directTypeExpr(subType), baseTypeExpr()), nilTypeName()),
        location=builtin),
      consExpr(lhs, consExpr(elem, nilExpr())),
      location=builtin);
  
  forwards to mkErrorCheck(localErrors, fwrd);
}

abstract production insertVector
top::Expr ::= lhs::Expr index::Expr elem::Expr
{
  propagate substituted;
  top.pp = pp"${lhs.pp}.insert(${index.pp}, ${elem.pp})";
  
  local subType::Type = vectorSubType(lhs.typerep, top.env);
  
  local localErrors::[Message] =
    checkVectorHeaderDef("_insert_vector", top.location, top.env) ++
    (if index.typerep.isIntegerType
     then []
     else [err(index.location, s"Vector insertion index must have integer type, but got ${showType(index.typerep)}")]) ++
    (if !compatibleTypes(subType, index.typerep, true, false)
     then [err(top.location, s"Inserted type must be the same as vector sub-type, got ${showType(subType)} and ${showType(index.typerep)}")]
     else []);

  local fwrd::Expr =
    callExpr(
      templateDeclRefExpr(
        name("_insert_vector", location=builtin),
        consTypeName(typeName(directTypeExpr(subType), baseTypeExpr()), nilTypeName()),
        location=builtin),
      consExpr(lhs, consExpr(index, consExpr(elem, nilExpr()))),
      location=builtin);
  
  forwards to mkErrorCheck(localErrors, fwrd);
}

abstract production extendVector
top::Expr ::= e1::Expr e2::Expr
{
  propagate substituted;
  top.pp = pp"${e1.pp}.extend(${e2.pp})";
  
  local subType::Type = vectorSubType(e1.typerep, top.env);
  
  local localErrors::[Message] =
    checkVectorHeaderDef("_extend_vector", top.location, top.env) ++
    if !compatibleTypes(subType, vectorSubType(e2.typerep, top.env), true, false)
    then [err(top.location, s"Vector extend sub-types must be the same, got ${showType(e1.typerep)} and ${showType(e2.typerep)}")]
    else [];

  local fwrd::Expr =
    callExpr(
      templateDeclRefExpr(
        name("_extend_vector", location=builtin),
        consTypeName(typeName(directTypeExpr(subType), baseTypeExpr()), nilTypeName()),
        location=builtin),
      consExpr(e1, consExpr(e2, nilExpr())),
      location=builtin);
  
  forwards to mkErrorCheck(localErrors, fwrd);
}

abstract production showVector
top::Expr ::= e::Expr
{
  propagate substituted;
  top.pp = pp"show(${e.pp})";
  
  local subType::Type = vectorSubType(e.typerep, top.env);

  local localErrors::[Message] =
    checkVectorHeaderDef("_show_vector", top.location, top.env) ++
    checkShowErrors(subType, top.env, top.location);
  local fwrd::Expr =
    callExpr(
      templateDeclRefExpr(
        name("_show_vector", location=builtin),
        consTypeName(typeName(directTypeExpr(subType), baseTypeExpr()), nilTypeName()),
        location=builtin),
      consExpr(e, nilExpr()),
      location=builtin);
  
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
