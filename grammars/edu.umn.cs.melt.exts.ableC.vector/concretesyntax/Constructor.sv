grammar edu:umn:cs:melt:exts:ableC:vector:concretesyntax;

marking terminal Vec_t /vec[\ ]*</ lexer classes {Ckeyword};

concrete productions top::PrimaryExpr_c
| Vec_t sub::TypeName_c '>' init::VectorInitializer_c
  { top.ast = init.ast;
    init.subTypeIn = sub.ast; }

inherited attribute subTypeIn::TypeName;

nonterminal VectorInitializer_c with location, ast<Expr>, subTypeIn;

concrete productions top::VectorInitializer_c
| '[' elems::VectorConstructorExprList_c ']'
  { top.ast = constructVector(top.subTypeIn, foldExpr(elems.ast), location=top.location); }
| '[' ']'
  { top.ast = constructVector(top.subTypeIn, nilExpr(), location=top.location); }
| '(' size::AssignExpr_c ')'
  { top.ast = newVector(top.subTypeIn, size.ast, location=top.location); }

-- Can't use ArgumentExprList due to mda restrictions
closed nonterminal VectorConstructorExprList_c with location, ast<[Expr]>;

concrete productions top::VectorConstructorExprList_c
| e::AssignExpr_c
    { top.ast = [e.ast]; }
| h::VectorConstructorExprList_c ',' t::AssignExpr_c
    { top.ast = h.ast ++ [t.ast];  }
