grammar edu:umn:cs:melt:exts:ableC:vector:concretesyntax;

marking terminal Vec_t 'vec' lexer classes {Cidentifier}, font=font_all;

aspect parser attribute context
  action {
    context = addIdentsToScope([name("vec", location=builtin)], Vec_t, context);
  };

concrete productions top::PrimaryExpr_c
| 'vec' '<' sub::TypeName_c '>' '(' args::ArgumentExprList_c ')' '[' elems::VectorConstructorExprList_c ']'
  { top.ast = constructVector(sub.ast, foldExpr(args.ast), foldExpr(elems.ast), location=top.location); }
| 'vec' '<' sub::TypeName_c '>' '(' args::ArgumentExprList_c ')' '[' ']'
  { top.ast = constructVector(sub.ast, foldExpr(args.ast), nilExpr(), location=top.location); }
| 'vec' '<' sub::TypeName_c '>' '[' elems::VectorConstructorExprList_c ']'
  { top.ast = constructVector(sub.ast, nilExpr(), foldExpr(elems.ast), location=top.location); }
| 'vec' '<' sub::TypeName_c '>' '[' ']'
  { top.ast = constructVector(sub.ast, nilExpr(), nilExpr(), location=top.location); }
| 'vec' '(' args::ArgumentExprList_c ')' '[' elems::VectorConstructorExprList_c ']'
  { top.ast = inferredConstructVector(foldExpr(args.ast), foldExpr(elems.ast), location=top.location); }
  -- Illegal, but AST provides a better error
| 'vec' '(' args::ArgumentExprList_c ')' '[' ']'
  { top.ast = inferredConstructVector(foldExpr(args.ast), nilExpr(), location=top.location); }
| 'vec' '[' elems::VectorConstructorExprList_c ']'
  { top.ast = inferredConstructVector(nilExpr(), foldExpr(elems.ast), location=top.location); }
  -- Illegal, but AST provides a better error
| 'vec' '[' ']'
  { top.ast = inferredConstructVector(nilExpr(), nilExpr(), location=top.location); }

-- Can't use ArgumentExprList due to mda restrictions
closed nonterminal VectorConstructorExprList_c with location, ast<[Expr]>;

concrete productions top::VectorConstructorExprList_c
| e::AssignExpr_c
    { top.ast = [e.ast]; }
| h::VectorConstructorExprList_c ',' t::AssignExpr_c
    { top.ast = h.ast ++ [t.ast];  }
