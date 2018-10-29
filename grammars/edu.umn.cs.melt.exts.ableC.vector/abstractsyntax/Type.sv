grammar edu:umn:cs:melt:exts:ableC:vector:abstractsyntax;

import edu:umn:cs:melt:ableC:abstractsyntax:overloadable;

abstract production vectorTypeExpr 
top::BaseTypeExpr ::= q::Qualifiers sub::TypeName loc::Location
{
  propagate substituted;
  top.pp = pp"${terminate(space(), q.pps)}vector<${sub.pp}>";
  
  sub.env = globalEnv(top.env);
  
  local localErrors::[Message] =
    sub.errors ++ checkVectorHeaderDef("_vector_s", loc, top.env);
  
  forwards to
    if !null(localErrors)
    then errorTypeExpr(localErrors)
    else
      injectGlobalDeclsTypeExpr(
        foldDecl([
          templateTypeExprInstDecl(
            q,
            name("_vector_s", location=builtin),
            consTypeName(sub, nilTypeName()))]),
        extTypeExpr(q, vectorType(sub.typerep)));
}

abstract production vectorType
top::ExtType ::= sub::Type
{
  propagate substituted;
  top.pp = pp"vector<${sub.lpp}${sub.rpp}>";
  top.host =
    pointerType(
      top.givenQualifiers,
      extType(
        nilQualifier(),
        refIdExtType(
          structSEU(),
          templateMangledName("_vector_s", [sub]),
          templateMangledRefId("_vector_s", [sub]))));
  top.mangledName = s"vector_${sub.mangledName}_";
  top.isEqualTo =
    \ other::ExtType ->
      case other of
        vectorType(otherSub) -> compatibleTypes(sub, otherSub, false, false)
      | _ -> false
      end;
  
  top.lAddProd = just(concatVector(_, _, location=_));
  top.rAddProd = just(concatVector(_, _, location=_));
  -- Overload for += automatically inferred from above
  top.lEqualsProd = just(equalsVector(_, _, location=_));
  top.rEqualsProd = just(equalsVector(_, _, location=_));
  -- Overload for != automatically inferred from above
  top.addressOfArraySubscriptProd = just(addressOfSubscriptVector(_, _, location=_));
  -- Overloads for [], []= automatically inferred from above
  top.callMemberProd = just(callMemberVector(_, _, _, _, location=_));
  top.memberProd = just(memberVector(_, _, _, location=_));
  top.showProd = just(showVector(_, location=_));
}

-- Find the sub-type of a vector type
function vectorSubType
Type ::= t::Type
{
  return
    case t of
      extType(_, vectorType(sub)) -> sub
    | _ -> errorType()
    end;
}
