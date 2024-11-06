grammar edu:umn:cs:melt:exts:ableC:vector:concretesyntax;

marking terminal Vec_t 'vec' lexer classes {Keyword, Global};

concrete productions top::PrimaryExpr_c
| 'vec' '<' sub::TypeName_c '>' '[' elems::VectorConstructorExprList_c ']'
  { top.ast = constructVector(sub.ast, foldr(consVectorExpr, nilVectorExpr(), elems.ast)); }
| 'vec' '<' sub::TypeName_c '>' '[' ']'
  { top.ast = constructVector(sub.ast, nilVectorExpr()); }
| 'vec' '[' elems::VectorConstructorExprList_c ']'
  { top.ast = inferredConstructVector(foldr(consVectorExpr, nilVectorExpr(), elems.ast)); }
  -- Illegal, but AST provides a better error
| 'vec' '[' ']'
  { top.ast = inferredConstructVector(nilVectorExpr()); }

-- Can't use ArgumentExprList due to mda restrictions
closed tracked nonterminal VectorConstructorExprList_c with ast<[Expr]>;

concrete productions top::VectorConstructorExprList_c
| e::AssignExpr_c
    { top.ast = [e.ast]; }
| h::VectorConstructorExprList_c ',' t::AssignExpr_c
    { top.ast = h.ast ++ [t.ast];  }
