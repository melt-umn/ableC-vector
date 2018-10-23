grammar edu:umn:cs:melt:exts:ableC:vector:concretesyntax;

marking terminal Vec_t /vec[\ ]*</ lexer classes {Ckeyword};
terminal Allocate_t 'allocate';

concrete productions top::PrimaryExpr_c
| Vec_t sub::TypeName_c '>' init::VectorInitializer_c
  { top.ast = init.ast;
    init.subTypeIn = sub.ast; }

inherited attribute subTypeIn::TypeName;

nonterminal VectorInitializer_c with location, ast<Expr>, subTypeIn;

concrete productions top::VectorInitializer_c
| allocator::MaybeAllocator_c '[' elems::VectorConstructorExprList_c ']'
  { top.ast = constructVector(top.subTypeIn, allocator.ast.fst, allocator.ast.snd, foldExpr(elems.ast), location=top.location); }
| allocator::MaybeAllocator_c '[' ']'
  { top.ast = constructVector(top.subTypeIn, allocator.ast.fst, allocator.ast.snd, nilExpr(), location=top.location); }
| allocator::MaybeAllocator_c '(' size::AssignExpr_c ')'
  { top.ast = newVector(top.subTypeIn, allocator.ast.fst, allocator.ast.snd, size.ast, location=top.location); }

nonterminal MaybeAllocator_c with ast<Pair<MaybeExpr MaybeExpr>>, location;

concrete productions top::MaybeAllocator_c
| 'allocate' '(' e1::AssignExpr_c ',' e2::AssignExpr_c ')'
    { top.ast = pair(justExpr(e1.ast), justExpr(e2.ast)); }
| 
    { top.ast = pair(nothingExpr(), nothingExpr()); }

-- Can't use ArgumentExprList due to mda restrictions
closed nonterminal VectorConstructorExprList_c with location, ast<[Expr]>;

concrete productions top::VectorConstructorExprList_c
| e::AssignExpr_c
    { top.ast = [e.ast]; }
| h::VectorConstructorExprList_c ',' t::AssignExpr_c
    { top.ast = h.ast ++ [t.ast];  }
