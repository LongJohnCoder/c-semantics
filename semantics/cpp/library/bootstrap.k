module LIBCPP-BOOTSTRAP-SYNTAX
     imports CPP-DYNAMIC-SORTS

     syntax Expr ::= builtin(QualId, Val) [klabel(builtin1Cpp)]
                   | builtin(QualId) [klabel(builtin0Cpp)]

     syntax KItem ::= "initCPPBuiltins"

     syntax K ::= "initException" [function]

endmodule

module LIBCPP-BOOTSTRAP
     imports LIBCPP-BOOTSTRAP-SYNTAX
     imports LIB-BUILTIN-SYNTAX
     imports C-CONFIGURATION
     imports COMMON-BUILTIN-SYNTAX
     imports CPP-DYNAMIC-SYNTAX
     imports CPP-STMT-RETURN-SYNTAX
     imports CPP-SYNTAX
     imports CPP-TYPING-SYNTAX

     syntax Expr ::= prepareBuiltin(QualId, Bool, StrictList, StrictList) [klabel(prepareBuiltinCpp)]

     context prepareBuiltin(_, _, (HOLE:StrictList => prval(HOLE)), _)

     context prepareBuiltin(_, _, _, (HOLE:StrictList => prval(HOLE)))

     rule <k> callBuiltin
              => Return''(prepareBuiltin(F, variadic in getParams(T),
                   list(filterList(makeNamesFromCIds(P), notVarArg)),
                   list(filterList(makeNamesFromCIds(P), isVarArg))))
          ...</k>
          <curr-scope> blockScope(_, Base::SymBase, _) </curr-scope>
          <functions>... Base |-> functionObject(F::QualId, T::CPPType, _, _) ...</functions>
          <curr-function-params> P::List </curr-function-params>

     syntax List ::= makeNamesFromCIds(List) [function]
     rule makeNamesFromCIds(.List) => .List
     rule makeNamesFromCIds(ListItem(X::CId) L::List) => ListItem(makeNameFromCId(X)) makeNamesFromCIds(L)

     syntax ExecName ::= makeNameFromCId(CId) [function]

     rule makeNameFromCId(X::CId) => ExecName(NoNNS(), X)

     rule prepareBuiltin(Q::QualId, false, krlist(.List), krlist(.List))
          => builtin(Q)

     rule prepareBuiltin(Q::QualId, false, krlist(ListItem(V::Val)), krlist(.List))
          => builtin(Q, V)

     rule initCPPBuiltins => initException

endmodule
