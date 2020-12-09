module C-TRANSLATION-INIT
     imports BOOL
     imports LIST
     imports STRING
     imports COMPAT-SYNTAX
     imports OPTIONS-SYNTAX
     imports SETTINGS-SYNTAX
     imports C-ABSTRACT-SYNTAX
     imports C-COMMON-PROMOTION-SYNTAX
     imports C-CONFIGURATION
     imports C-CONVERSION-SYNTAX
     imports C-DECL-INITIALIZER-SYNTAX
     imports C-DECL-RESOLUTION-SYNTAX
     imports C-DYNAMIC-SYNTAX
     imports C-ELABORATOR-SYNTAX
     imports C-SYNTAX
     imports C-TYPING-EXPR-SYNTAX
     imports C-TYPING-INTERPRETATION
     imports C-TYPING-SYNTAX
     imports COMMON-INIT-SYNTAX
     imports COMMON-TRANSLATION-UNIT-SYNTAX

     rule <k> TranslationUnit(Tu:String, list(Strings:List), list(Decls:List))
               => makeTu(Tu +String Uuid)
               ~> preDeclareStrings(Strings)
               ~> listToK(Decls)
               ~> allocateIncompleteTentatives
               ~> removeUnusedIdentifiers(Tu +String Uuid)
          ...</k>
          <uuid> Uuid::String </uuid>

     syntax KItem ::= preDeclareStrings(List)
     rule preDeclareStrings(ListItem(K:KItem) L:List)
          => K ~> discard
          ~> preDeclareStrings(L)
          [structural]
     rule preDeclareStrings(.List) => .K
          [structural]

     rule CodeLoc(K:K, L:CabsLoc) => filterCabsLoc(L) ~> K
     rule DefinitionLocRange(K:KItem, L1:CabsLoc, L2:CabsLoc)
          => filterCabsLoc(L1) ~> K ~> filterCabsLoc(L2)

     rule <k> L:CabsLoc => .K ...</k>
          <elab>... .K => L </elab>
          <curr-program-loc> _ => L </curr-program-loc>

     syntax CabsLoc ::= filterCabsLoc(CabsLoc) [function]
     rule filterCabsLoc(CabsLoc("cabs loc unknown", _, -10, -10, _))
          => UnknownCabsLoc
     rule filterCabsLoc(L:CabsLoc) => L [owise]

     rule ExpressionLoc(K:K, L::CabsLoc) => ExpLoc(K, L)
     rule typeof(ExpLoc(K:K, L::CabsLoc) => K)
     rule utype(ExpLoc(K:K, L::CabsLoc) => K)
     rule type(ExpLoc(K:K, L::CabsLoc) => K)
     rule stripHold(ExpLoc(K:KItem, L::CabsLoc)) => ExpLoc(stripHold(K), L)

     rule isKResult(ExpLoc(K:K, _::CabsLoc)) => isKResult(K)
     rule isRValue(ExpLoc(K:K, _::CabsLoc)) => isRValue(K)
     rule isHold(ExpLoc(K:K, _::CabsLoc)) => isHold(K)
     rule fromConstantExpr(ExpLoc(te(...) #as V:RValue, _::CabsLoc)) => fromConstantExpr(V)  // false
     rule fromConstantExpr(ExpLoc(tv(...) #as V:RValue, _::CabsLoc)) => fromConstantExpr(V)  // true
     //rule fromConstantExpr(ExpLoc(V:RValue, _::CabsLoc)) => fromConstantExprStuck(V) requires notBool isRHold(V) 
     rule fromConstantExpr(ExpLoc(...) #as E) => fromConstantExprStuckLocation(E) [owise]

     syntax Bool ::= fromConstantExprStuck(RValue)  [function]
     syntax Bool ::= fromConstantExprStuckLocation(Location)  [function]
     syntax Bool ::= fromConstantExprStuckTe(Bool)  [function]
     syntax Bool ::= fromConstantExprStuckTv(Bool)  [function]

     syntax KItem ::= #freezerExpLoc(CabsLoc)

     rule
          <k> ExpLoc(K:K, L::CabsLoc) => K ~> #freezerExpLoc(L) ... </k>
          <curr-program-loc> _ => L </curr-program-loc>
          requires notBool isKResult(K)
     rule
          <k> (K:KItem ~> #freezerExpLoc(L::CabsLoc)) => ExpLoc(K, L) ... </k>
          <curr-program-loc> _ => L </curr-program-loc>
          requires isKResult(K) orBool isRValue(K)

     rule
          <k> reval(ExpLoc(K:RValue, L::CabsLoc) => K) ... </k>
          <curr-program-loc> _ => L </curr-program-loc>
     rule reval(ExpLoc(ExpLoc(K:K, _::CabsLoc) => K, _::CabsLoc))

     rule reval(ExpLoc(ncle(K:KItem, T::Type) => te(K, rvalType(T)), _::CabsLoc))
     //rule reval(ExpLoc(nclv(Loc::SymLoc, T::Type), _::CabsLoc) => nclv(Loc, T))

     rule (ExpLoc(ncle(K:KItem, T::Type), _::CabsLoc) => ncle(K, T)) ++
     rule (ExpLoc(ncle(K:KItem, T::Type), _::CabsLoc) => ncle(K, T)) --
     rule (ExpLoc(ncle(K:KItem, T::Type), _::CabsLoc) => ncle(K, T)) := _

     syntax KItem ::= leftExpLoc(CabsLoc) | rightExpLoc(CabsLoc)

     // bitwise.k
     rule ExpLoc(te(...) #as Te, L:CabsLoc) >> Right:RValue => Te >> Right ~> leftExpLoc(L)
     rule ExpLoc(tv(...) #as Tv, L:CabsLoc) >> Right:RValue => Tv >> Right ~> leftExpLoc(L)
     rule Left:RValue >> ExpLoc(te(...) #as Te, L:CabsLoc) => Left >> Te ~> rightExpLoc(L)
     rule Left:RValue >> ExpLoc(tv(...) #as Tv, L:CabsLoc) => Left >> Tv ~> rightExpLoc(L)
     rule te(Left:KItem >> Right:KItem, T:UType) ~> leftExpLoc(L:CabsLoc) => te(ExpLoc(Left, L) >> Right, T)
     rule te(Left:KItem >> Right:KItem, T:UType) ~> rightExpLoc(L:CabsLoc) => te(Left >> ExpLoc(Right, L), T)

     rule ExpLoc(te(...) #as Te, L:CabsLoc) << Right:RValue => Te << Right ~> leftExpLoc(L)
     rule ExpLoc(tv(...) #as Tv, L:CabsLoc) << Right:RValue => Tv << Right ~> leftExpLoc(L)
     rule Left:RValue << ExpLoc(te(...) #as Te, L:CabsLoc) => Left << Te ~> rightExpLoc(L)
     rule Left:RValue << ExpLoc(tv(...) #as Tv, L:CabsLoc) => Left << Tv ~> rightExpLoc(L)
     rule te(Left:KItem << Right:KItem, T:UType) ~> leftExpLoc(L:CabsLoc) => te(ExpLoc(Left, L) << Right, T)
     rule te(Left:KItem << Right:KItem, T:UType) ~> rightExpLoc(L:CabsLoc) => te(Left << ExpLoc(Right, L), T)

     // common/cast.k
     rule cast(T:UType, ExpLoc(tv(...) #as Tv, L:CabsLoc)) => cast(T, Tv)
     //rule tv(...) #as Tv:RValue ~> rightExpLoc(L:CabsLoc) => ExpLoc(Tv, L)

     rule L:Location & R:Location => te(stripHold(L) & stripHold(R), utype(L))
          requires (isHold(L) orBool isHold(R))
               andBool isPromoted(utype(L))
               andBool utype(L) ==Type utype(R)
               andBool notBool (fromConstantExpr(L) andBool /* xorBool in original */ fromConstantExpr(R))
               andBool isRValue(L) andBool isRValue(R)

     // translation/cast.k
     rule cast(T'::UType, ExpLoc(te(K:KItem, _), L:CabsLoc), E::Bool) => te(#Cast(type(T'), ExpLoc(K, L), E), T')

     // interpretation.k
     rule ArrayType(_, (ExpLoc(V:RValue, _) => V), _)

     // Assignment.k
     rule (ExpLoc(_:Nclv, _::CabsLoc) #as E1) *= E2:RValue
          => compoundAssign(E1, ncle(LHOLE, type(E1)) := te(RHOLE, utype(E1)) * E2)
     rule (ExpLoc(_:Nclv, _::CabsLoc) #as E1) /= E2:RValue
          => compoundAssign(E1, ncle(LHOLE, type(E1)) := te(RHOLE, utype(E1)) / E2)
     rule (ExpLoc(_:Nclv, _::CabsLoc) #as E1) %= E2:RValue
          => compoundAssign(E1, ncle(LHOLE, type(E1)) := te(RHOLE, utype(E1)) % E2)
     rule (ExpLoc(_:Nclv, _::CabsLoc) #as E1) += E2:RValue
          => compoundAssign(E1, ncle(LHOLE, type(E1)) := te(RHOLE, utype(E1)) + E2)
     rule (ExpLoc(_:Nclv, _::CabsLoc) #as E1) -= E2:RValue
          => compoundAssign(E1, ncle(LHOLE, type(E1)) := te(RHOLE, utype(E1)) - E2)
     rule (ExpLoc(_:Nclv, _::CabsLoc) #as E1) <<= E2:RValue
          => compoundAssign(E1, ncle(LHOLE, type(E1)) := te(RHOLE, utype(E1)) << E2)
     rule (ExpLoc(_:Nclv, _::CabsLoc) #as E1) >>= E2:RValue
          => compoundAssign(E1, ncle(LHOLE, type(E1)) := te(RHOLE, utype(E1)) >> E2)
     rule (ExpLoc(_:Nclv, _::CabsLoc) #as E1) &= E2:RValue
          => compoundAssign(E1, ncle(LHOLE, type(E1)) := te(RHOLE, utype(E1)) & E2)
     rule (ExpLoc(_:Nclv, _::CabsLoc) #as E1) ^= E2:RValue
          => compoundAssign(E1, ncle(LHOLE, type(E1)) := te(RHOLE, utype(E1)) ^ E2)
     rule (ExpLoc(_:Nclv, _::CabsLoc) #as E1) |= E2:RValue
          => compoundAssign(E1, ncle(LHOLE, type(E1)) := te(RHOLE, utype(E1)) | E2)

     rule (ExpLoc(E1:Nclv, _::CabsLoc) => E1) := _

     rule compoundAssign((ExpLoc(LV:Nclv, _::CabsLoc) => LV), AExp:RValue)

     // reference.k
     rule &(ExpLoc(E1:Nclv, _::CabsLoc) => E1)

     // inc-and-dec.k
     rule ++ (ExpLoc(E1:Nclv, _::CabsLoc) #as E) => E += tv(1, utype(int))
     rule -- (ExpLoc(E1:Nclv, _::CabsLoc) #as E) => E -= tv(1, utype(int))

     // members.k
     rule (ExpLoc(E1:Nclv, _::CabsLoc) => E1) . _:CId
          [structural]

     // initializer.k
     rule figureInit(_:CId, _:Type, SingleInit(ExpLoc(K:KItem, _::CabsLoc) => K))

     //interpretation.k
     rule BitFieldType(_::KItem, (ExpLoc(K:KItem, _::CabsLoc) => K))
          [structural]



     /*@ \fromStandard{\source[n1570]{\para{6.10.6}{1}}}{
     A preprocessing directive of the form
     \cdisplay{# pragma pp-tokensoptnew-line}
     \broken{where the preprocessing token \cinline{STDC} does not immediately
     follow pragma in the directive (prior to any macro replacement)} causes the
     implementation to behave in an implementation-defined manner. The behavior
     might cause translation to fail or cause the translator or the resulting
     program to behave in a non-conforming manner. Any such pragma that is not
     recognized by the implementation is ignored.
     }*/
     rule Pragma(_) => .K
          [structural]

     rule NothingExpression() => emptyValue

     rule [[ nameOfCurrentTranslationUnit() => Tu ]]
          <curr-tu> Tu::String </curr-tu>

     rule currentSemantics() => CTranslation()

     context alias [c]: HERE:K

     rule (<T>...
               <k> cleanup </k>
               <options> Opts:Set </options>
          ...</T> => .Bag)
          requires notBool (Debug() in Opts)
          [structural]
endmodule
