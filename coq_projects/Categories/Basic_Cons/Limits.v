From Categories Require Import Essentials.Notations.
From Categories Require Import Essentials.Types.
From Categories Require Import Essentials.Facts_Tactics.
From Categories Require Import Category.Main.
From Categories Require Import Functor.Main.
From Categories Require Import Limits.Limit.
From Categories Require Import Archetypal.Discr.Discr.
From Categories Require Import Cat.Terminal.
From Categories Require Import
        Basic_Cons.Terminal
        Basic_Cons.Product
        Basic_Cons.Equalizer
        Basic_Cons.PullBack
.
        

(** In this module we show that terminal objects, products, equalizers and
    pullbacks are limits. The corresponding duals are dually colimits. *)

Section Limits.
  Context {C : Category}.

  Section Terminal.

    Definition Terminal_Producing_Func_fun (x : Empty) : C
      :=
        match x with
        end
    .
    
    Context (L : Limit (Discr_Func Terminal_Producing_Func_fun)).

    Program Definition Terminal_as_Limit_Cone
            (c : C)
      :
        Cone (Discr_Func Terminal_Producing_Func_fun)
      :=
        {|
          cone_apex :=
            {|
              FO := fun _ => c;
              FA := fun _ _ _ => id
            |};
          cone_edge :=
            {|
              Trans :=
                fun x =>
                  match x with
                  end
            |}
        |}
    .


    Local Hint Extern 1 => match goal with [x : unit |- _] => destruct x end.
    Local Hint Extern 1 => rewrite From_Term_Cat.
    Local Hint Extern 1 => apply NatTrans_eq_simplify.
    Local Hint Extern 1 => progress cbn.
    
    Local Obligation Tactic := basic_simpl; auto 10.

    Program Definition Terminal_as_Limit_Cone_morph
            {c : C}
            (f : (c –≻ L)%morphism)
      :
        Cone_Morph _ (Terminal_as_Limit_Cone c) (LRKE L)
      :=
        {|
          cone_morph :=
            {|
              Trans :=
                fun c =>
                  match c as u return ( _ –≻ L _o u)%object%morphism with
                    tt => f
                  end
            |}
        |}
    .      
      
    Program Definition Terminal_as_Limit : (𝟙_ C)%object :=
      {|
        terminal := L;
        t_morph :=
          fun c =>
            Trans (LRKE_morph_ex L (Terminal_as_Limit_Cone c)) tt
      |}
    .

    Local Obligation Tactic := idtac.
    
    Next Obligation.
    Proof.    
      intros c f g.
      apply (
          f_equal
            (fun w : (Terminal_as_Limit_Cone c –≻ L)%nattrans => Trans w tt)
            (
              LRKE_morph_unique
                L
                _
                (Terminal_as_Limit_Cone_morph f)
                (Terminal_as_Limit_Cone_morph g)
            )
        ).
    Qed.

  End Terminal.
  
  Section Product.
    Context (a b : C).

    Definition Product_Producing_Func_fun (x : bool) : C
      :=
        match x with
        | true => a
        | false => b
        end
    .
    
    Context (L : Limit (Discr_Func Product_Producing_Func_fun)).

    Program Definition Product_as_Limit_Cone
            {p : C}
            (h : (p –≻ a)%morphism)
            (h' : (p –≻ b)%morphism)
      :
        Cone (Discr_Func Product_Producing_Func_fun)
      :=
        {|
          cone_apex :=
            {|
              FO := fun _ => p;
              FA := fun _ _ _ => id
            |};
          cone_edge :=
            {|
              Trans :=
                fun x =>
                  match x with
                  | true => h
                  | false => h'
                  end
            |}
        |}
    .

    Local Hint Extern 1 => match goal with [x : unit |- _] => destruct x end.
    Local Hint Extern 1 => match goal with [x : bool |- _] => destruct x end.
    Local Hint Extern 1 => rewrite From_Term_Cat.
    Local Hint Extern 1 => apply NatTrans_eq_simplify.
    Local Hint Extern 1 => progress cbn.
    

    Local Obligation Tactic := basic_simpl; auto 10.
    
    Program Definition Product_as_Limit_Cone_morph
            {p : C}
            (h : (p –≻ a)%morphism)
            (h' : (p –≻ b)%morphism)
            (f : (p –≻ L)%morphism)
            (H1 : (Trans L true ∘ f)%morphism = h)
            (H2 : (Trans L false ∘ f)%morphism = h')
      :
        Cone_Morph _ (Product_as_Limit_Cone h h') (LRKE L)
      :=
        {|
          cone_morph :=
            {|
              Trans :=
                fun c =>
                  match c as u return ( _ –≻ L _o u)%object%morphism with
                    tt => f
                  end
            |}
        |}
    .
    
    Program Definition Product_as_Limit : (a × b)%object :=
      {|
        product := L;
        Pi_1 := Trans (cone_edge L) true;
        Pi_2 := Trans (cone_edge L) false;
        Prod_morph_ex :=
          fun p h h' =>
            Trans (LRKE_morph_ex L (Product_as_Limit_Cone h h')) tt
      |}
    .

    Local Obligation Tactic := idtac.

    Next Obligation.
    Proof.
      intros p h h'.
      cbn.
      set (H :=
             f_equal
               (fun w
                    :
                      (Product_as_Limit_Cone h h'
                 ∘ Functor_To_1_Cat (Discr_Cat Datatypes.bool)
                 –≻ Discr_Func Product_Producing_Func_fun)%nattrans
                => Trans w true)
               (cone_morph_com (LRKE_morph_ex L (Product_as_Limit_Cone h h')))
          ).
      cbn in H.
      rewrite From_Term_Cat in H.
      auto.
    Qed.

    Next Obligation.
    Proof.
      intros p h h'.
      set (H :=
             f_equal
               (fun w
                    :
                      ((Product_as_Limit_Cone h h')
                         ∘ Functor_To_1_Cat (Discr_Cat Datatypes.bool)
                         –≻ Discr_Func Product_Producing_Func_fun)%nattrans
                => Trans w false)
               (cone_morph_com (LRKE_morph_ex L (Product_as_Limit_Cone h h')))
          ).
      cbn in H.
      rewrite From_Term_Cat in H.
      auto.
    Qed.
    
    Next Obligation.
    Proof.    
      intros p h h' f g H1 H2 H3 H4.
      apply (
          f_equal
            (fun w : (Product_as_Limit_Cone h h' –≻ L)%nattrans => Trans w tt)
            (
              LRKE_morph_unique
                L
                _
                (Product_as_Limit_Cone_morph _ _ _ H1 H2)
                (Product_as_Limit_Cone_morph _ _ _ H3 H4)
            )
        ).
    Qed.

  End Product.

  Section Equalizer.
    Context {a b : C} (f g : (a –≻ b)%morphism).

    Local Hint Extern 1 => match goal with [x : unit |- _] => destruct x end.
    Local Hint Extern 1 => match goal with [x : Empty |- _] => destruct x end.
    Local Hint Extern 1 => match goal with [x : bool |- _] => destruct x end.
    Local Hint Extern 1 => rewrite From_Term_Cat.
    Local Hint Extern 1 => apply NatTrans_eq_simplify.
    Local Hint Extern 1 => progress cbn.
    

    Local Obligation Tactic := basic_simpl; auto 10.
    
    Program Definition Equalizer_Producing_Cat : Category
      :=
        {|
          Obj := bool;
          Hom :=
            fun x y =>
              match (x, y) with
              | (true, true) => unit
              | (true, false) => bool
              | (false, true) => Empty
              | (false, false) => unit
              end;
          compose :=
            fun x y z h h'=> _;
          id := fun x => _
        |}
    .

    Next Obligation.
    Proof.
      destruct x; destruct y; destruct z; auto.
    Defined.

    Next Obligation.
    Proof.    
      destruct x; constructor.
    Defined.

    Program Definition Equalizer_Producing_Func :
      (Equalizer_Producing_Cat –≻ C)%functor
      :=
        {|
          FO :=
            fun x =>
              match x with
              | true => a
              | false => b
              end;
          FA := fun x y h => _
        |}
    .

    Next Obligation.
    Proof.
      destruct x; destruct y.
      exact id.
      destruct h.
      {
        exact f.
      }
      {
        exact g.
      }
      destruct h.
      exact id.
    Defined.
    
    Context (L : Limit Equalizer_Producing_Func).
    
    Program Definition Equalizer_as_Limit_Cone
            {p : C}
            {h : (p –≻ a)%morphism}
            (H : (f ∘ h)%morphism = (g ∘ h)%morphism)
      :
        Cone Equalizer_Producing_Func
      :=
        {|
          cone_apex :=
            {|
              FO := fun _ => p;
              FA := fun _ _ _ => id
            |};
          cone_edge :=
            {|
              Trans :=
                fun x =>
                  match x with
                  | true => h
                  | false => (f ∘ h)%morphism
                  end
            |}
        |}
    .

    Local Obligation Tactic := idtac.

    Program Definition Equalizer_as_Limit_Cone_morph
            {p : C}
            {h : (p –≻ a)%morphism}
            (H1 : (f ∘ h)%morphism = (g ∘ h)%morphism)
            (k : (p –≻ L)%morphism)
            (H2 : (Trans L true ∘ k)%morphism = h)
      :
        Cone_Morph _ (Equalizer_as_Limit_Cone H1) (LRKE L)
      :=
        {|
          cone_morph :=
            {|
              Trans :=
                fun c =>
                  match c as u return ( _ –≻ L _o u)%object%morphism with
                    tt => k
                  end
            |}
        |}
    .      

    Next Obligation.
    Proof.
      basic_simpl; auto 10.
    Qed.

    Next Obligation.
    Proof.
      basic_simpl; auto 10.
    Qed.
      
    Next Obligation.
    Proof.
      intros p h H1 k H2.
      apply NatTrans_eq_simplify.
      extensionality x.
      cbn in *.
      destruct x; auto.
      rewrite assoc_sym.
      cbn_rewrite (@Trans_com _ _ _ _ L true false false).
      rewrite assoc.
      rewrite H1; rewrite <- H2.
      trivial.
    Qed.
      
    Program Definition Equalizer_as_Limit : Equalizer f g :=
      {|
        equalizer := L;
        equalizer_morph := Trans L true;
        equalizer_morph_ex :=
          fun e eqm H =>
            Trans (LRKE_morph_ex L (Equalizer_as_Limit_Cone H)) tt
      |}
    .

    Local Obligation Tactic := idtac.

    Next Obligation.
    Proof.
      set (H := @Trans_com _ _ _ _ L true false false).
      cbn in H.
      cbn_rewrite (@Trans_com _ _ _ _ L true false true) in H.
      trivial.
    Qed.

    Next Obligation.
    Proof.
      intros e eqm eqmc; cbn.
      cbn_rewrite (
          f_equal
            (fun w :
                   ((Equalizer_as_Limit_Cone eqmc)
                      ∘ Functor_To_1_Cat Equalizer_Producing_Cat
                      –≻ Equalizer_Producing_Func)%nattrans
             => Trans w true)
            (cone_morph_com (LRKE_morph_ex L (Equalizer_as_Limit_Cone eqmc)))
        ).
      auto.
    Qed.

    Next Obligation.
    Proof.
      intros e eqm H1 h h' H2 H3.
      apply (
          f_equal
            (fun w : (Equalizer_as_Limit_Cone H1 –≻ L)%nattrans => Trans w tt)
            (
              LRKE_morph_unique
                L
                _
                (Equalizer_as_Limit_Cone_morph _ _ H2)
                (Equalizer_as_Limit_Cone_morph _ _ H3)
            )
        ).
    Qed.

  End Equalizer.

  Section PullBack.
    Context
      {a b c : C}
      (f : (a –≻ c)%morphism)
      (g : (b –≻ c)%morphism)
    .
    
    Inductive PBType :=
    | PB_A
    | PB_B
    | PB_C
    .
      
    Local Hint Extern 1 => match goal with [x : unit |- _] => destruct x end.
    Local Hint Extern 1 => match goal with [x : PBType |- _] => destruct x end.
    Local Hint Extern 1 => match goal with [x : Empty |- _] => destruct x end.
    Local Hint Extern 1 => match goal with [x : bool |- _] => destruct x end.
    Local Hint Extern 1 => match goal with [|- unit] => constructor end.
    Local Hint Extern 1 => rewrite From_Term_Cat.
    Local Hint Extern 1 => apply NatTrans_eq_simplify.
    Local Hint Extern 1 => progress cbn.
    
    Local Obligation Tactic := basic_simpl; auto 10.
    
    Program Definition PullBack_Producing_Cat : Category
      :=
        {|
          Obj := PBType;
          Hom :=
            fun x y =>
              match (x, y) with
              | (PB_A, PB_A) => unit
              | (PB_A, PB_B) => Empty
              | (PB_A, PB_C) => unit
              | (PB_B, PB_A) => Empty
              | (PB_B, PB_B) => unit
              | (PB_B, PB_C) => unit
              | (PB_C, PB_A) => Empty
              | (PB_C, PB_B) => Empty
              | (PB_C, PB_C) => unit
              end;
          compose :=
            fun x y z h h'=> _;
          id := fun x => _
        |}
    .

    Program Definition PullBack_Producing_Func :
      (PullBack_Producing_Cat –≻ C)%functor
      :=
        {|
          FO :=
            fun x =>
              match x with
              | PB_A => a
              | PB_B => b
              | PB_C => c
              end;
          FA := fun x y h => _
        |}
    .

    Next Obligation.
    Proof.
      destruct x; destruct y; auto; try exact id.
    Defined.
    
    Context (L : Limit PullBack_Producing_Func).
    
    Program Definition PullBack_as_Limit_Cone
            {p : C}
            {h : (p –≻ a)%morphism}
            {h' : (p –≻ b)%morphism}
            (H : (f ∘ h)%morphism = (g ∘ h')%morphism)
      :
        Cone PullBack_Producing_Func
      :=
        {|
          cone_apex :=
            {|
              FO := fun _ => p;
              FA := fun _ _ _ => id
            |};
          cone_edge :=
            {|
              Trans :=
                fun x =>
                  match x with
                  | PB_A => h
                  | PB_B => h'
                  | PB_C => (f ∘ h)%morphism
                  end
            |}
        |}
    .

    Local Obligation Tactic := idtac.


    Program Definition PullBack_as_Limit_Cone_morph
            {p : C}
            {h : (p –≻ a)%morphism}
            {h' : (p –≻ b)%morphism}
            (H1 : (f ∘ h)%morphism = (g ∘ h')%morphism)
            (k : (p –≻ L)%morphism)
            (H2 : (Trans L PB_A ∘ k)%morphism = h)
            (H3 : (Trans L PB_B ∘ k)%morphism = h')
      :
        Cone_Morph _ (PullBack_as_Limit_Cone H1) (LRKE L)
      :=
        {|
          cone_morph :=
            {|
              Trans :=
                fun c =>
                  match c as u return ( _ –≻ L _o u)%object%morphism with
                    tt => k
                  end
            |}
        |}
    .      

    Next Obligation.
    Proof.
      basic_simpl; auto 10.
    Qed.

    Next Obligation.
    Proof.
      basic_simpl; auto 10.
    Qed.
      
    Next Obligation.
    Proof.
      intros p h h' H1 k H2 H3.
      apply NatTrans_eq_simplify.
      extensionality x.
      cbn in *.
      destruct x; auto.
      rewrite assoc_sym.
      cbn_rewrite (@Trans_com _ _ _ _ L PB_B PB_C tt).
      rewrite assoc.
      rewrite H1; rewrite <- H3.
      trivial.
    Qed.
    
    Program Definition PullBack_as_Limit : PullBack f g :=
      {|
        pullback := L;
        pullback_morph_1 := Trans L PB_A;
        pullback_morph_2 := Trans L PB_B;
        pullback_morph_ex :=
          fun e pm1 pm2 pmc =>
            Trans (LRKE_morph_ex L (PullBack_as_Limit_Cone pmc)) tt
      |}
    .

    Local Obligation Tactic := idtac.

    Next Obligation.
    Proof.
      set (H := @Trans_com _ _ _ _ L PB_B PB_C tt).
      cbn in H.
      cbn_rewrite (@Trans_com _ _ _ _ L PB_A PB_C tt) in H.
      trivial.
    Qed.

    Next Obligation.
    Proof.
      intros e pm1 pm2 pmc; cbn.
      cbn_rewrite (
          f_equal
            (fun w :
                   ((PullBack_as_Limit_Cone pmc)
                      ∘ Functor_To_1_Cat PullBack_Producing_Cat
                      –≻ PullBack_Producing_Func)%nattrans
             => Trans w PB_A)
            (cone_morph_com (LRKE_morph_ex L (PullBack_as_Limit_Cone pmc)))
        ).
      auto.
    Qed.

    Next Obligation.
    Proof.
      intros e pm1 pm2 pmc; cbn.
      cbn_rewrite (
          f_equal
            (fun w :
                   ((PullBack_as_Limit_Cone pmc)
                      ∘ Functor_To_1_Cat PullBack_Producing_Cat
                      –≻ PullBack_Producing_Func)%nattrans
             => Trans w PB_B)
            (cone_morph_com (LRKE_morph_ex L (PullBack_as_Limit_Cone pmc)))
        ).
      auto.
    Qed.
    
    Next Obligation.
    Proof.
      intros e pm1 pm2 H1 h h' H2 H3 H4 H5.
      apply (
          f_equal
            (fun w : (PullBack_as_Limit_Cone H1 –≻ L)%nattrans => Trans w tt)
            (
              LRKE_morph_unique
                L
                _
                (PullBack_as_Limit_Cone_morph _ _ H2 H3)
                (PullBack_as_Limit_Cone_morph _ _ H4 H5)
            )
        ).
    Qed.

  End PullBack.

End Limits.
