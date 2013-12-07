(** Remove already ported things from top *)
Section notation.
  Global Class FunctorApplicationInterpretable
         {C D} (F : Functor C D)
         {argsT : Type} (args : argsT)
         {T : Type} (rtn : T)
    := {}.

  Definition FunctorApplicationOf {C D} F {argsT} args {T} {rtn}
             `{@FunctorApplicationInterpretable C D F argsT args T rtn}
    := rtn.

  Global Arguments FunctorApplicationOf / {C} {D} F {argsT} args {T} {rtn} {_}.

  Global Instance FunctorApplicationObject C D (F : Functor C D) (x : C)
  : FunctorApplicationInterpretable F x (F x) | 0.

  Global Instance FunctorApplicationDash C D (F : Functor C D)
  : FunctorApplicationInterpretable F (IdentityFunctor C) F | 0.

  Global Instance FunctorApplicationFunctorTerminal C D (F : Functor C D) (c : C)
  : FunctorApplicationInterpretable F (FunctorFromTerminal _ c) (F c) | 0.

  Global Instance FunctorApplicationFunctor B C D (F : Functor C D) (G : Functor B C)
  : FunctorApplicationInterpretable F G (F ∘ G)%functor | 100.

  Global Instance FunctorApplicationObjObj A B D (F : Functor (A * B) D) (a : A) (b : B)
  : FunctorApplicationInterpretable F (a, b) (F (a, b)) | 100.

  Global Instance FunctorApplicationObjFunctorTerminal A B D (F : Functor (A * B) D) (a : A) (b : B)
  : FunctorApplicationInterpretable F (a, FunctorFromTerminal _ b) (F (a, b)) | 0.

  Global Instance FunctorApplicationFunctorTerminalObj A B D (F : Functor (A * B) D) (a : A) (b : B)
  : FunctorApplicationInterpretable F (FunctorFromTerminal _ a, b) (F (a, b)) | 0.

  Global Instance FunctorApplicationFunctorTerminalFunctorFromTerminal A B D (F : Functor (A * B) D) (a : A) (b : B)
  : FunctorApplicationInterpretable F (FunctorFromTerminal _ a, FunctorFromTerminal _ b) (F (a, b)) | 0.

  Global Instance FunctorApplicationObjFunctor A B C D (F : Functor (A * B) D) (a : A) (F' : Functor C B)
  : FunctorApplicationInterpretable F (a, F') (InducedProductSndFunctor F a ∘ F')%functor | 10.

  Global Instance FunctorApplicationObjIdentity A B D (F : Functor (A * B) D) (a : A)
  : FunctorApplicationInterpretable F (a, IdentityFunctor B) (InducedProductSndFunctor F a)%functor | 5.

  Global Instance FunctorApplicationFunctorObj A B C D (F : Functor (A^op * B) D) (F' : Functor C A) (b : B)
  : FunctorApplicationInterpretable F (F', b) (InducedProductFstFunctor F b ∘ F'^op)%functor | 10.

  Global Instance FunctorApplicationIdentityObj A B D (F : Functor (A * B) D) (b : B)
  : FunctorApplicationInterpretable F (IdentityFunctor A, b) (InducedProductFstFunctor F b)%functor | 5.

  (** Do we want this?  (to special case pairs of functors from the
      same category, so that, e.g., if [F : C * C -> D], then [F ⟨ ─ ,
      ─ ⟩] would be the diagonal functor [C -> D], ather than [F]
      itself.  Freenode says:

   freenode / ##categorytheory / jgross  2013-08-03 18:19  ()
       If F is a functor C * C -> D, and you see F(─, ─), how do you interpret it?
   freenode / ##categorytheory / jgross  2013-08-03 18:21  ()
       In particular, is it the functor C -> D which factors through F and the diagonal functor C -> C * C, or is it F itself?
-> freenode / ##categorytheory / Eduard_Munteanu  2013-08-03 18:21  (Eduard_Munteanu!~Eduard_Mu@188.25.7.132)
       jgross: F itself, I'd say
   freenode / ##categorytheory / jgross  2013-08-03 18:22  ()
       Ok, thanks.
   freenode / ##categorytheory / Eduard_Munteanu  2013-08-03 18:22  (Eduard_Munteanu!~Eduard_Mu@188.25.7.132)
       jgross: https://en.wikipedia.org/wiki/Hom_functor#Internal_Hom_functor seems to use that interpretation too
   freenode / ##categorytheory / Cale  2013-08-03 18:23  (Cale!~Cale@99.247.222.118)
       jgross: By * do you mean × ?
   freenode / ##categorytheory / Cale  2013-08-03 18:23  (Cale!~Cale@99.247.222.118)
       (I suppose you do)
   freenode / ##categorytheory / Eduard_Munteanu  2013-08-03 18:23  (Eduard_Munteanu!~Eduard_Mu@188.25.7.132)
       Actually https://en.wikipedia.org/wiki/Hom_functor#Formal_definition too, near the end
   freenode / ##categorytheory / Cale  2013-08-03 18:23  (Cale!~Cale@99.247.222.118)
       In any case, yeah, I would say it would mean F itself.
   freenode / ##categorytheory / jgross  2013-08-03 18:27  ()
       Yes, by * I mean ×.
 *)
  (**  Global Instance FunctorApplicationFunctorFunctor A B C D (F : Functor (A * B) D) (G : Functor C A) (H : Functor C B)
  : FunctorApplicationInterpretable F (G, H) (F ∘ (FunctorProduct G H))%functor | 10.*)

  Global Instance FunctorApplicationFunctorFunctor' A B C C' D (F : Functor (A^op * B) D) (G : Functor C A) (H : Functor C' B)
  : FunctorApplicationInterpretable F (G, H) (F ∘ (FunctorProduct' G^op H))%functor | 100.
End notation.

(** First, a bunch of notations for display *)
Notation "F ⟨ a , F' ⟨ 1 ⟩ ⟩" := (InducedProductSndFunctor F a^op ∘ F')%functor : functor_scope.
Notation "F ⟨ F' ⟨ 1 ⟩ , b ⟩" := (InducedProductFstFunctor F b^op ∘ F')%functor : functor_scope.
Notation "F ⟨ a , 1 ⟩" := (InducedProductSndFunctor F a^op)%functor : functor_scope.
Notation "F ⟨ 1 , b ⟩" := (InducedProductFstFunctor F b^op)%functor : functor_scope.
Notation "F ⟨ a , b ⟩" := (F (a, b)) : functor_scope.
Notation "F ⟨ G ⟨ 1 ⟩ , H ⟨ 1 ⟩ ⟩" := (F ∘ (FunctorProduct' G^op H))%functor : functor_scope.
Notation "F ⟨ 1 , H ⟨ 1 ⟩ ⟩" := (F ∘ (FunctorProduct' (IdentityFunctor _) H))%functor : functor_scope.
Notation "F ⟨ G ⟨ 1 ⟩ , 1 ⟩" := (F ∘ (FunctorProduct' G^op (IdentityFunctor _)))%functor : functor_scope.

(** Now, the fully general notation so the defaults can parse *)
Notation "F ⟨ x ⟩" := (FunctorApplicationOf F%functor x%functor) : functor_scope.
Notation "F ⟨ x , y ⟩" := (FunctorApplicationOf F%functor (x%functor , y%functor)) : functor_scope.

(** Now, the default notations, so that anything we don't cover can
    parse, and everything parses in terms of the general notation *)
Notation "F ⟨ 1 ⟩" := (F ⟨ ( 1 ) ⟩)%functor : functor_scope.
Notation "F ⟨ x , 1 ⟩" := (F ⟨ x , ( 1 ) ⟩)%functor : functor_scope.
Notation "F ⟨ 1 , y ⟩" := (F ⟨ ( 1 ) , y ⟩)%functor : functor_scope.
Notation "F ⟨ 1 , 1 ⟩" := (F ⟨ ( 1 ) , ( 1 ) ⟩)%functor : functor_scope.
Notation "F ⟨ x ⟨ 1 ⟩ ⟩" := (F ⟨ ( x ⟨ 1 ⟩ ) ⟩)%functor : functor_scope.
Notation "F ⟨ x ⟨ 1 ⟩ , y ⟨ 1 ⟩ ⟩" := (F ⟨ ( x ⟨ 1 ⟩ ) , ( y ⟨ 1 ⟩ ) ⟩)%functor : functor_scope.
Notation "F ⟨ x , y ⟨ 1 ⟩ ⟩" := (F ⟨ x , ( y ⟨ 1 ⟩ ) ⟩)%functor : functor_scope.
Notation "F ⟨ 1 , y ⟨ 1 ⟩ ⟩" := (F ⟨ ( 1 ) , ( y ⟨ 1 ⟩ ) ⟩)%functor : functor_scope.
Notation "F ⟨ x ⟨ 1 ⟩ , y ⟩" := (F ⟨ ( x ⟨ 1 ⟩ ) , y ⟩)%functor : functor_scope.
Notation "F ⟨ x ⟨ 1 ⟩ , 1 ⟩" := (F ⟨ ( x ⟨ 1 ⟩ ) , ( 1 ) ⟩)%functor : functor_scope.

(** Redefine the general notation, so it takes precedence when it can *)
Notation "F ⟨ x ⟩" := (FunctorApplicationOf F%functor x%functor) : functor_scope.
Notation "F ⟨ x , y ⟩" := (FunctorApplicationOf F%functor (x%functor , y%functor)) : functor_scope.
(*Notation "F ⟨ c , - ⟩" := (InducedProductSndFunctor F c) : functor_scope.
Notation "F ⟨ - , d ⟩" := (InducedProductFstFunctor F d) : functor_scope.*)
