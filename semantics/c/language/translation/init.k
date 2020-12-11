module C-TRANSLATION-INIT
     imports BOOL
     imports LIST
     imports STRING
     imports COMPAT-SYNTAX
     imports OPTIONS-SYNTAX
     imports SETTINGS-SYNTAX
     imports C-ABSTRACT-SYNTAX
     imports C-CHECK-USE-SYNTAX
     imports C-COMMON-PROMOTION-SYNTAX
     imports C-CONFIGURATION
     imports C-CONVERSION-SYNTAX
     imports C-DECL-INITIALIZER-SYNTAX
     imports C-DECL-RESOLUTION-SYNTAX
     imports C-DECL-TAGGED
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

     rule ExpressionLoc(K:K, L:CabsLoc) => ExpLoc(K, L)

     rule typeof(ExpLoc(K:K, _:CabsLoc) => K)
     rule utype(ExpLoc(K:K, _:CabsLoc) => K)
     rule type(ExpLoc(K:K, _:CabsLoc) => K)
     rule stripHold(ExpLoc(K:KItem, L::CabsLoc)) => ExpLoc(stripHold(K), L)
     rule value(ExpLoc(K:K, _:CabsLoc) => K)
     rule fromConstantExpr(ExpLoc(V:RValue, _::CabsLoc)) => fromConstantExpr(V)
     rule isNullPointerConstant(ExpLoc(V:RValue, _:CabsLoc)) => isNullPointerConstant(V)

     rule isKResult(ExpLoc(K:K, _::CabsLoc)) => isKResult(K) andBool notBool isTv(K)
     //rule isRValue(ExpLoc(K:K, _::CabsLoc)) => isRValue(K) andBool notBool isTv(K)
     rule isHold(ExpLoc(K:K, _::CabsLoc)) => isHold(K)

     syntax Bool ::= isTv(K)  [function]
     rule isTv(tv(...)) => true
     rule isTv(_) => false [owise]

     syntax KItem ::= #popExpLoc()

     rule
          <k> ExpLoc(K:K, L::CabsLoc) => K ~> #popExpLoc() ... </k>
          <curr-expression-loc> .List => ListItem(L) ...</curr-expression-loc>
          requires notBool isKResult(K)
     rule ExpLoc(tv(...) #as Tv:RValue, _::CabsLoc) => Tv

     rule <k> te(K:RValue, T:UType) ~> #popExpLoc() => te(ExpLoc(K, L), T) ... </k>
          <curr-expression-loc> ListItem(L:CabsLoc) => .List ...</curr-expression-loc>
          requires notBool isLocation(K)
     rule <k> te(ExpLoc(K:RValue, _), T:UType) ~> #popExpLoc() => te(ExpLoc(K, L), T) ... </k>
          <curr-expression-loc> ListItem(L:CabsLoc) => .List ...</curr-expression-loc>
          requires notBool isLocation(K)  // The requires clause should never be needed.

     rule <k> ncle(K:KItem, T:Type) ~> #popExpLoc() => ncle(ExpLoc(K, L), T) ... </k>
          <curr-expression-loc> ListItem(L:CabsLoc) => .List ...</curr-expression-loc>
          requires notBool isLocation(K)
     rule <k> ncle(ExpLoc(K:KItem, _), T:Type) ~> #popExpLoc() => ncle(ExpLoc(K, L), T) ... </k>
          <curr-expression-loc> ListItem(L:CabsLoc) => .List ...</curr-expression-loc>
          requires notBool isLocation(K)  // Should never be needed.

     // TODO: Fix this:
     rule <k> nclv(...) ~> (#popExpLoc() => .K) ... </k>
          <curr-expression-loc> ListItem(L:CabsLoc) => .List ...</curr-expression-loc>
     /*
     rule <k> nclv(...) #as Nclv:Nclv ~> #popExpLoc() => ExpLoc(Nclv, L) ... </k>
          <curr-expression-loc> ListItem(L:CabsLoc) => .List ...</curr-expression-loc>
     rule <k> ExpLoc(nclv(...) #as Nclv:Nclv, _) ~> #popExpLoc() => ExpLoc(Nclv, L) ... </k>
          <curr-expression-loc> ListItem(L:CabsLoc) => .List ...</curr-expression-loc>
     rule <k> reval(ExpLoc(nclv(...) #as Nclv:Nclv, L::CabsLoc))
               => reval(Nclv) ~> #popExpLoc()
          ...</k>
          <curr-expression-loc> .List => ListItem(L) ...</curr-expression-loc>
          [priority(25)]
     */

     rule <k> V:RValue ~> (#popExpLoc() => .K) ... </k>
          <curr-expression-loc> ListItem(_:CabsLoc) => .List ...</curr-expression-loc>
          requires notBool isRHold(V)
     rule <k> reval(V:RValue) ~> (#popExpLoc() => .K) ... </k>
          <curr-expression-loc> ListItem(_:CabsLoc) => .List ...</curr-expression-loc>

     /*
     rule
          <k> reval(ExpLoc(K:K, L::CabsLoc)) => reval(K) ~> #freezerExpLoc(L) ... </k>
          <curr-program-loc> _ => L </curr-program-loc>
          requires notBool isRValue(K)  // Works only in the C semantics
     rule reval(ExpLoc(ExpLoc(K:K, _::CabsLoc) => K, _::CabsLoc))
     rule <k> reval(V:RValue) ~> #freezerExpLoc(L) => reval(ExpLoc(V, L)) ...</k>
          <curr-program-loc> _ => L </curr-program-loc>

     //rule reval(ExpLoc(ncle(K:KItem, T::Type) => te(K, rvalType(T)), _::CabsLoc))
     //rule reval(ExpLoc(nclv(Loc::SymLoc, T::Type), _::CabsLoc) => nclv(Loc, T))

     rule nclv(...) #as V:Nclv ~> rightExpLoc(L:CabsLoc) => ExpLoc(V, L)
     rule te(...) #as V:RHold ~> rightExpLoc(L:CabsLoc) => ExpLoc(V, L)

     rule (ExpLoc(ncle(K:KItem, T::Type), _:CabsLoc) => ncle(K, T)) ++
     rule (ExpLoc(ncle(K:KItem, T::Type), _:CabsLoc) => ncle(K, T)) --
     rule (ExpLoc(ncle(K:KItem, T::Type), _:CabsLoc) => ncle(K, T)) := _

     // tagged.k
     rule initEnum(X:CId, (ExpLoc(tv(...) #as V:RValue, _:CabsLoc) => V))

     // translation/assignment.k
     rule L:Nclv := ExpLoc(R:RValue, Loc:CabsLoc) => L := R ~> rightExpLoc(Loc)
     rule te(L:Nclv := R:RValue, T:UType) ~> rightExpLoc(Loc:CabsLoc) => te(L := ExpLoc(R, Loc), T)

     // unary.k
     rule - ExpLoc(te(...) #as Te, L:CabsLoc) => - Te ~> rightExpLoc(L)
     rule - ExpLoc(tv(...) #as Tv, L:CabsLoc) => - Tv ~> rightExpLoc(L)
     rule te(- Right:KItem, T:UType) ~> rightExpLoc(L:CabsLoc) => te(- ExpLoc(Right, L), T)

     rule + ExpLoc(te(...) #as Te, L:CabsLoc) => + Te ~> rightExpLoc(L)
     rule + ExpLoc(tv(...) #as Tv, L:CabsLoc) => + Tv ~> rightExpLoc(L)
     rule te(+ Right:KItem, T:UType) ~> rightExpLoc(L:CabsLoc) => te(+ ExpLoc(Right, L), T)

     rule ! ExpLoc(te(...) #as Te, L:CabsLoc) => ! Te ~> rightExpLoc(L)
     rule ! ExpLoc(tv(...) #as Tv, L:CabsLoc) => ! Tv ~> rightExpLoc(L)
     rule te(! Right:KItem, T:UType) ~> rightExpLoc(L:CabsLoc) => te(! ExpLoc(Right, L), T)

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

     rule ExpLoc(te(...) #as Te, L:CabsLoc) & Right:RValue => Te & Right ~> leftExpLoc(L)
     rule ExpLoc(tv(...) #as Tv, L:CabsLoc) & Right:RValue => Tv & Right ~> leftExpLoc(L)
     rule Left:RValue & ExpLoc(te(...) #as Te, L:CabsLoc) => Left & Te ~> rightExpLoc(L)
     rule Left:RValue & ExpLoc(tv(...) #as Tv, L:CabsLoc) => Left & Tv ~> rightExpLoc(L)
     rule te(Left:KItem & Right:KItem, T:UType) ~> leftExpLoc(L:CabsLoc) => te(ExpLoc(Left, L) & Right, T)
     rule te(Left:KItem & Right:KItem, T:UType) ~> rightExpLoc(L:CabsLoc) => te(Left & ExpLoc(Right, L), T)

     rule ExpLoc(te(...) #as Te, L:CabsLoc) | Right:RValue => Te | Right ~> leftExpLoc(L)
     rule ExpLoc(tv(...) #as Tv, L:CabsLoc) | Right:RValue => Tv | Right ~> leftExpLoc(L)
     rule Left:RValue | ExpLoc(te(...) #as Te, L:CabsLoc) => Left | Te ~> rightExpLoc(L)
     rule Left:RValue | ExpLoc(tv(...) #as Tv, L:CabsLoc) => Left | Tv ~> rightExpLoc(L)
     rule te(Left:KItem | Right:KItem, T:UType) ~> leftExpLoc(L:CabsLoc) => te(ExpLoc(Left, L) | Right, T)
     rule te(Left:KItem | Right:KItem, T:UType) ~> rightExpLoc(L:CabsLoc) => te(Left | ExpLoc(Right, L), T)

     rule ExpLoc(te(...) #as Te, L:CabsLoc) ^ Right:RValue => Te ^ Right ~> leftExpLoc(L)
     rule ExpLoc(tv(...) #as Tv, L:CabsLoc) ^ Right:RValue => Tv ^ Right ~> leftExpLoc(L)
     rule Left:RValue ^ ExpLoc(te(...) #as Te, L:CabsLoc) => Left ^ Te ~> rightExpLoc(L)
     rule Left:RValue ^ ExpLoc(tv(...) #as Tv, L:CabsLoc) => Left ^ Tv ~> rightExpLoc(L)
     rule te(Left:KItem ^ Right:KItem, T:UType) ~> leftExpLoc(L:CabsLoc) => te(ExpLoc(Left, L) ^ Right, T)
     rule te(Left:KItem ^ Right:KItem, T:UType) ~> rightExpLoc(L:CabsLoc) => te(Left ^ ExpLoc(Right, L), T)

     rule ~ ExpLoc(te(...) #as Te, L:CabsLoc) => ~ Te ~> rightExpLoc(L)
     rule ~ ExpLoc(tv(...) #as Tv, L:CabsLoc) => ~ Tv ~> rightExpLoc(L)
     rule te(~ Right:KItem, T:UType) ~> rightExpLoc(L:CabsLoc) => te(~ ExpLoc(Right, L), T)

     // multiplicative.k

     rule ExpLoc(te(...) #as Te, L:CabsLoc) * Right:RValue => Te * Right ~> leftExpLoc(L)
     rule ExpLoc(tv(...) #as Tv, L:CabsLoc) * Right:RValue => Tv * Right ~> leftExpLoc(L)
     rule Left:RValue * ExpLoc(te(...) #as Te, L:CabsLoc) => Left * Te ~> rightExpLoc(L)
     rule Left:RValue * ExpLoc(tv(...) #as Tv, L:CabsLoc) => Left * Tv ~> rightExpLoc(L)
     rule te(Left:KItem * Right:KItem, T:UType) ~> leftExpLoc(L:CabsLoc) => te(ExpLoc(Left, L) * Right, T)
     rule te(Left:KItem * Right:KItem, T:UType) ~> rightExpLoc(L:CabsLoc) => te(Left * ExpLoc(Right, L), T)

     rule ExpLoc(te(...) #as Te, L:CabsLoc) / Right:RValue => Te / Right ~> leftExpLoc(L)
     rule ExpLoc(tv(...) #as Tv, L:CabsLoc) / Right:RValue => Tv / Right ~> leftExpLoc(L)
     rule Left:RValue / ExpLoc(te(...) #as Te, L:CabsLoc) => Left / Te ~> rightExpLoc(L)
     rule Left:RValue / ExpLoc(tv(...) #as Tv, L:CabsLoc) => Left / Tv ~> rightExpLoc(L)
     rule te(Left:KItem / Right:KItem, T:UType) ~> leftExpLoc(L:CabsLoc) => te(ExpLoc(Left, L) / Right, T)
     rule te(Left:KItem / Right:KItem, T:UType) ~> rightExpLoc(L:CabsLoc) => te(Left / ExpLoc(Right, L), T)

     rule ExpLoc(te(...) #as Te, L:CabsLoc) % Right:RValue => Te % Right ~> leftExpLoc(L)
     rule ExpLoc(tv(...) #as Tv, L:CabsLoc) % Right:RValue => Tv % Right ~> leftExpLoc(L)
     rule Left:RValue % ExpLoc(te(...) #as Te, L:CabsLoc) => Left % Te ~> rightExpLoc(L)
     rule Left:RValue % ExpLoc(tv(...) #as Tv, L:CabsLoc) => Left % Tv ~> rightExpLoc(L)
     rule te(Left:KItem % Right:KItem, T:UType) ~> leftExpLoc(L:CabsLoc) => te(ExpLoc(Left, L) % Right, T)
     rule te(Left:KItem % Right:KItem, T:UType) ~> rightExpLoc(L:CabsLoc) => te(Left % ExpLoc(Right, L), T)

     // additive.k

     rule ExpLoc(te(...) #as Te, L:CabsLoc) + Right:RValue => Te + Right ~> leftExpLoc(L)
     rule ExpLoc(tv(...) #as Tv, L:CabsLoc) + Right:RValue => Tv + Right ~> leftExpLoc(L)
     rule Left:RValue + ExpLoc(te(...) #as Te, L:CabsLoc) => Left + Te ~> rightExpLoc(L)
     rule Left:RValue + ExpLoc(tv(...) #as Tv, L:CabsLoc) => Left + Tv ~> rightExpLoc(L)
     rule te(Left:KItem + Right:KItem, T:UType) ~> leftExpLoc(L:CabsLoc) => te(ExpLoc(Left, L) + Right, T)
     rule te(Left:KItem + Right:KItem, T:UType) ~> rightExpLoc(L:CabsLoc) => te(Left + ExpLoc(Right, L), T)

     rule ExpLoc(te(...) #as Te, L:CabsLoc) - Right:RValue => Te - Right ~> leftExpLoc(L)
     rule ExpLoc(tv(...) #as Tv, L:CabsLoc) - Right:RValue => Tv - Right ~> leftExpLoc(L)
     rule Left:RValue - ExpLoc(te(...) #as Te, L:CabsLoc) => Left - Te ~> rightExpLoc(L)
     rule Left:RValue - ExpLoc(tv(...) #as Tv, L:CabsLoc) => Left - Tv ~> rightExpLoc(L)
     rule te(Left:KItem - Right:KItem, T:UType) ~> leftExpLoc(L:CabsLoc) => te(ExpLoc(Left, L) - Right, T)
     rule te(Left:KItem - Right:KItem, T:UType) ~> rightExpLoc(L:CabsLoc) => te(Left - ExpLoc(Right, L), T)

     rule tv(...) #as Tv:RValue ~> rightExpLoc(L:CabsLoc) => ExpLoc(Tv, L)
     rule tv(...) #as Tv:RValue ~> leftExpLoc(L:CabsLoc) => ExpLoc(Tv, L)

     rule ExpLoc(tv(...) #as Tv:RValue, _:CabsLoc) ~> rightExpLoc(L:CabsLoc) => ExpLoc(Tv, L)
     rule ExpLoc(tv(...) #as Tv:RValue, _:CabsLoc) ~> leftExpLoc(L:CabsLoc) => ExpLoc(Tv, L)

     // relational.k

     rule ExpLoc(te(...) #as Te, L:CabsLoc) < Right:RValue => Te < Right ~> leftExpLoc(L)
     rule ExpLoc(tv(...) #as Tv, L:CabsLoc) < Right:RValue => Tv < Right ~> leftExpLoc(L)
     rule Left:RValue < ExpLoc(te(...) #as Te, L:CabsLoc) => Left < Te ~> rightExpLoc(L)
     rule Left:RValue < ExpLoc(tv(...) #as Tv, L:CabsLoc) => Left < Tv ~> rightExpLoc(L)
     rule te(Left:KItem < Right:KItem, T:UType) ~> leftExpLoc(L:CabsLoc) => te(ExpLoc(Left, L) < Right, T)
     rule te(Left:KItem < Right:KItem, T:UType) ~> rightExpLoc(L:CabsLoc) => te(Left < ExpLoc(Right, L), T)

     rule ExpLoc(te(...) #as Te, L:CabsLoc) <= Right:RValue => Te <= Right ~> leftExpLoc(L)
     rule ExpLoc(tv(...) #as Tv, L:CabsLoc) <= Right:RValue => Tv <= Right ~> leftExpLoc(L)
     rule Left:RValue <= ExpLoc(te(...) #as Te, L:CabsLoc) => Left <= Te ~> rightExpLoc(L)
     rule Left:RValue <= ExpLoc(tv(...) #as Tv, L:CabsLoc) => Left <= Tv ~> rightExpLoc(L)
     rule te(Left:KItem <= Right:KItem, T:UType) ~> leftExpLoc(L:CabsLoc) => te(ExpLoc(Left, L) <= Right, T)
     rule te(Left:KItem <= Right:KItem, T:UType) ~> rightExpLoc(L:CabsLoc) => te(Left <= ExpLoc(Right, L), T)

     rule ExpLoc(te(...) #as Te, L:CabsLoc) == Right:RValue => Te == Right ~> leftExpLoc(L)
     rule ExpLoc(tv(...) #as Tv, L:CabsLoc) == Right:RValue => Tv == Right ~> leftExpLoc(L)
     rule Left:RValue == ExpLoc(te(...) #as Te, L:CabsLoc) => Left == Te ~> rightExpLoc(L)
     rule Left:RValue == ExpLoc(tv(...) #as Tv, L:CabsLoc) => Left == Tv ~> rightExpLoc(L)
     rule te(Left:KItem == Right:KItem, T:UType) ~> leftExpLoc(L:CabsLoc) => te(ExpLoc(Left, L) == Right, T)
     rule te(Left:KItem == Right:KItem, T:UType) ~> rightExpLoc(L:CabsLoc) => te(Left == ExpLoc(Right, L), T)

     rule ExpLoc(te(...) #as Te, L:CabsLoc) != Right:RValue => Te != Right ~> leftExpLoc(L)
     rule ExpLoc(tv(...) #as Tv, L:CabsLoc) != Right:RValue => Tv != Right ~> leftExpLoc(L)
     rule Left:RValue != ExpLoc(te(...) #as Te, L:CabsLoc) => Left != Te ~> rightExpLoc(L)
     rule Left:RValue != ExpLoc(tv(...) #as Tv, L:CabsLoc) => Left != Tv ~> rightExpLoc(L)
     rule te(Left:KItem != Right:KItem, T:UType) ~> leftExpLoc(L:CabsLoc) => te(ExpLoc(Left, L) != Right, T)
     rule te(Left:KItem != Right:KItem, T:UType) ~> rightExpLoc(L:CabsLoc) => te(Left != ExpLoc(Right, L), T)

     rule ExpLoc(te(...) #as Te, L:CabsLoc) >= Right:RValue => Te >= Right ~> leftExpLoc(L)
     rule ExpLoc(tv(...) #as Tv, L:CabsLoc) >= Right:RValue => Tv >= Right ~> leftExpLoc(L)
     rule Left:RValue >= ExpLoc(te(...) #as Te, L:CabsLoc) => Left >= Te ~> rightExpLoc(L)
     rule Left:RValue >= ExpLoc(tv(...) #as Tv, L:CabsLoc) => Left >= Tv ~> rightExpLoc(L)
     rule te(Left:KItem >= Right:KItem, T:UType) ~> leftExpLoc(L:CabsLoc) => te(ExpLoc(Left, L) >= Right, T)
     rule te(Left:KItem >= Right:KItem, T:UType) ~> rightExpLoc(L:CabsLoc) => te(Left >= ExpLoc(Right, L), T)

     rule ExpLoc(te(...) #as Te, L:CabsLoc) > Right:RValue => Te > Right ~> leftExpLoc(L)
     rule ExpLoc(tv(...) #as Tv, L:CabsLoc) > Right:RValue => Tv > Right ~> leftExpLoc(L)
     rule Left:RValue > ExpLoc(te(...) #as Te, L:CabsLoc) => Left > Te ~> rightExpLoc(L)
     rule Left:RValue > ExpLoc(tv(...) #as Tv, L:CabsLoc) => Left > Tv ~> rightExpLoc(L)
     rule te(Left:KItem > Right:KItem, T:UType) ~> leftExpLoc(L:CabsLoc) => te(ExpLoc(Left, L) > Right, T)
     rule te(Left:KItem > Right:KItem, T:UType) ~> rightExpLoc(L:CabsLoc) => te(Left > ExpLoc(Right, L), T)

     // reference.k

     rule * ExpLoc(te(...) #as Te, L:CabsLoc) => * Te ~> rightExpLoc(L)
     rule * ExpLoc(tv(...) #as Tv, L:CabsLoc) => * Tv ~> rightExpLoc(L)
     rule te(* V:KItem, T:UType) ~> rightExpLoc(L:CabsLoc) => te(* ExpLoc(V, L), T)  // Do I need this?
     rule ncle(* V:KItem, T:Type) ~> rightExpLoc(L:CabsLoc) => ncle(* ExpLoc(V, L), T)

     rule & ExpLoc(te(...) #as Te, L:CabsLoc) => & Te ~> rightExpLoc(L)
     rule & ExpLoc(tv(...) #as Tv, L:CabsLoc) => & Tv ~> rightExpLoc(L)
     rule te(& V:KItem, T:UType) ~> rightExpLoc(L:CabsLoc) => te(& ExpLoc(V, L), T)

     // translation/function-call.k

     rule <k>Call(ExpLoc(tv(...) #as Tv, L:CabsLoc), A:KItem) => Call(Tv, A) ~> rightExpLoc(L) ...</k>
          <curr-program-loc> _ => L </curr-program-loc>
     rule te(Call(checkUse(V:RValue), A:KItem), T:UType) ~> rightExpLoc(L:CabsLoc) => te(Call(checkUse(ExpLoc(V, L)), A), T)

     // common/cast.k
     rule cast(T:UType, ExpLoc(tv(...) #as Tv, L:CabsLoc)) => cast(T, Tv)
     rule cast(T:UType, ExpLoc(tv(...) #as Tv, L:CabsLoc), Explicit:Bool) => cast(T, Tv, Explicit)

     // translation/cast.k
     rule cast(T'::UType, ExpLoc(te(K:KItem, _), L:CabsLoc), E::Bool) => te(#Cast(type(T'), ExpLoc(K, L), E), T')
     */

     // interpretation.k
     rule ArrayType(_, (ExpLoc(V:RValue, _) => V), _)

     /*
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
     */

     // TODO: Something better.
     // initializer.k
     rule figureInit(_:CId, _:Type, SingleInit(ExpLoc(K:KItem, _::CabsLoc) => K))

     /*

     //interpretation.k
     rule BitFieldType(_::KItem, (ExpLoc(K:KItem, _::CabsLoc) => K))
          [structural]
     */



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
