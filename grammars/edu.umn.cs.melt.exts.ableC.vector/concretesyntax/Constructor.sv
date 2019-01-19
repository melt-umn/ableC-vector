grammar edu:umn:cs:melt:exts:ableC:vector:concretesyntax;

marking terminal VecLT_t /vec[\ ]*</ lexer classes {Ckeyword};
marking terminal Vec_t   'vec'       lexer classes {Ckeyword};

concrete productions top::PrimaryExpr_c
| VecLT_t sub::TypeName_c '>' '(' args::ArgumentExprList_c ')' '[' elems::VectorConstructorExprList_c ']'
  { top.ast = constructVector(sub.ast, foldExpr(args.ast), foldExpr(elems.ast), location=top.location); }
| VecLT_t sub::TypeName_c '>' '(' args::ArgumentExprList_c ')' '[' ']'
  { top.ast = constructVector(sub.ast, foldExpr(args.ast), nilExpr(), location=top.location); }
| VecLT_t sub::TypeName_c '>' '[' elems::VectorConstructorExprList_c ']'
  { top.ast = constructVector(sub.ast, nilExpr(), foldExpr(elems.ast), location=top.location); }
| VecLT_t sub::TypeName_c '>' '[' ']'
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
