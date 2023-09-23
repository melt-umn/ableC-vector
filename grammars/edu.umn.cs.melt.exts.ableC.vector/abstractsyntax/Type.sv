grammar edu:umn:cs:melt:exts:ableC:vector:abstractsyntax;

import edu:umn:cs:melt:ableC:abstractsyntax:overloadable;

abstract production vectorTypeExpr 
top::BaseTypeExpr ::= q::Qualifiers sub::TypeName loc::Location
{
  top.pp = pp"${terminate(space(), q.pps)}vector<${sub.pp}>";
  propagate controlStmtContext;
  
  top.inferredArgs := sub.inferredArgs;
  sub.argumentType =
    case top.argumentType of
    | extType(_, vectorType(t)) -> t
    | _ -> errorType()
    end;
  
  sub.env = globalEnv(top.env);
  
  local localErrors::[Message] =
    sub.errors ++ checkVectorHeaderDef("_vector_s", loc, top.env);
  
  forwards to
    if !null(localErrors)
    then errorTypeExpr(localErrors)
    else
      injectGlobalDeclsTypeExpr(
        foldDecl(
          sub.decls ++
          [templateTypeExprInstDecl(
            q, name("_vector_s", location=builtin),
            consTemplateArg(typeTemplateArg(sub.typerep), nilTemplateArg()))]),
        extTypeExpr(q, vectorType(sub.typerep)));
}

abstract production vectorType
top::ExtType ::= sub::Type
{
  propagate canonicalType;
  top.pp = pp"vector<${sub.lpp}${sub.rpp}>";
  top.host =
    pointerType(
      top.givenQualifiers,
      extType(
        nilQualifier(),
        refIdExtType(
          structSEU(),
          just(templateMangledName("_vector_s", foldTemplateArg([typeTemplateArg(sub)]))),
          templateMangledRefId("_vector_s", foldTemplateArg([typeTemplateArg(sub)])))));
  top.mangledName = s"vector_${sub.mangledName}_";
  top.isEqualTo =
    \ other::ExtType ->
      case other of
        vectorType(otherSub) -> compatibleTypes(sub, otherSub, false, false)
      | _ -> false
      end;
  
  top.newProd = just(newVector(sub, _, location=_));
  top.deleteProd = just(deleteVector(_));
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
  top.objectInitProd = just(vectorInitializer(_, location=_));
  
  top.showErrors =
    \ l::Location env::Decorated Env ->
      sub.showErrors(l, env) ++
      checkVectorHeaderDef("show_vector", l, env);
  top.showProd =
    \ e::Expr -> ableC_Expr { inst show_vector<$directTypeExpr{sub}>($Expr{e}) };
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
