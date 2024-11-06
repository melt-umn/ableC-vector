grammar edu:umn:cs:melt:exts:ableC:vector:abstractsyntax;

abstract production vectorTypeExpr 
top::BaseTypeExpr ::= q::Qualifiers sub::TypeName
{
  top.pp = pp"${terminate(space(), q.pps)}vector<${sub.pp}>";
  
  top.inferredArgs := sub.inferredArgs;
  sub.argumentType =
    case top.argumentType of
    | extType(_, vectorType(t)) -> ^t
    | _ -> errorType()
    end;
  
  local localErrors::[Message] =
    sub.errors ++ checkVectorHeaderDef(top.env);

  forward fwrd =
    injectGlobalDeclsTypeExpr(
      consDecl(
        typePreDecls(@sub),
        consDecl(
          templateTypeExprInstDecl(
            ^q, name("_vector_s"),
            consTemplateArg(typeTemplateArg(sub.typerep), nilTemplateArg())),
          nilDecl())),
      extTypeExpr(@q, vectorType(sub.typerep)));

  forwards to if null(localErrors) then @fwrd else errorTypeExpr(localErrors);
}

abstract production vectorType
top::ExtType ::= sub::Type
{
  propagate canonicalType;
  top.pp = pp"vector<${sub.lpp}${sub.rpp}>";

  local templateArgs::TemplateArgs = consTemplateArg(typeTemplateArg(@sub), nilTemplateArg());
  top.host =
    pointerType(
      top.givenQualifiers,
      extType(
        nilQualifier(),
        refIdExtType(
          structSEU(),
          just(templateArgs.templateMangledName("_vector_s")),
          templateArgs.templateMangledRefId("_vector_s"))));
  top.mangledName = s"vector_${sub.mangledName}_";
  top.isEqualTo =
    \ other::ExtType ->
      case other of
        vectorType(otherSub) -> compatibleTypes(^sub, ^otherSub, false, false)
      | _ -> false
      end;

  top.lAddProd = just(concatVector);
  top.rAddProd = just(concatVector);
  -- Overload for += automatically inferred from above
  top.lEqualsProd = just(equalsVector);
  top.rEqualsProd = just(equalsVector);
  -- Overload for != automatically inferred from above
  top.arraySubscriptProd = just(subscriptVector);
  top.memberCallProd = just(callMemberVector);
  top.memberProd = just(memberVector);
  top.objectInitProd = just(vectorInitializer);
  
  top.showErrors := \ env::Env -> sub.showErrors(env) ++ checkVectorHeaderDef(env);
  top.showMaxLenProd = \ e::Expr -> ableC_Expr {
    inst show_vector_max_len<$directTypeExpr{^sub}>($Expr{e})
  };
  top.showProd = \ buf::Expr e::Expr -> ableC_Expr {
    inst show_vector_to_buf<$directTypeExpr{^sub}>($Expr{buf}, $Expr{e})
  };
}

-- Find the sub-type of a vector type
fun vectorSubType Type ::= t::Type =
  case t of
  | extType(_, vectorType(sub)) -> ^sub
  | _ -> errorType()
  end;
