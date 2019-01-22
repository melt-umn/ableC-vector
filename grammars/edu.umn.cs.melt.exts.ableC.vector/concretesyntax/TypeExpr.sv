grammar edu:umn:cs:melt:exts:ableC:vector:concretesyntax;

imports edu:umn:cs:melt:ableC:concretesyntax;
imports silver:langutil only ast;

imports edu:umn:cs:melt:ableC:abstractsyntax:host;
imports edu:umn:cs:melt:ableC:abstractsyntax:construction;
imports edu:umn:cs:melt:ableC:abstractsyntax:env;
--imports edu:umn:cs:melt:ableC:abstractsyntax:debug;

imports edu:umn:cs:melt:exts:ableC:vector:abstractsyntax;

marking terminal Vector_t 'vector' lexer classes {Cidentifier, Ctype};

aspect parser attribute context
  action {
    context = addIdentsToScope([name("vector", location=builtin)], Vector_t, context);
  };

concrete productions top::TypeSpecifier_c
| 'vector' '<' sub::TypeName_c '>'
    { top.realTypeSpecifiers = [vectorTypeExpr(top.givenQualifiers, sub.ast, top.location)];
      top.preTypeSpecifiers = []; }
