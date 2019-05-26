(** The contents in this file are reconstructed from the proof of Bruno Barras
 ** in the Coq standard library. It is duplicated so that the definitions
 ** can be made transparent, and therefore computable.
 ** See Coq.Logic.Eqdep_dec for complete information
 **)
Section uip_trans.
  Context {A : Type}.

  Definition uip_prop_trans (dec : forall x y : A, x = y \/ x <> y)
    {x : A} :
    forall {y : A} (pf pf' : x = y), pf = pf' :=
    let comp :=
        fun (x y y' : A) (eq1 : x = y) (eq2 : x = y') =>
          eq_ind x (fun a : A => a = y') eq2 y eq1 in
    let eq_dec := dec x in
    let nu :=
        fun (y : A) (u : x = y) =>
          match eq_dec y with
          | or_introl eqxy => eqxy
          | or_intror neqxy => False_ind (x = y) (neqxy u)
          end in
    let nu_constant :=
        fun (y : A) (u v : x = y) =>
          let o := eq_dec y in
          match
            o as o0
            return
            (match o0 with
             | or_introl eqxy => eqxy
             | or_intror neqxy => False_ind (x = y) (neqxy u)
             end =
             match o0 with
             | or_introl eqxy => eqxy
             | or_intror neqxy => False_ind (x = y) (neqxy v)
             end)
          with
          | or_introl Heq => eq_refl
          | or_intror Hneq =>
            match
              Hneq u as f
              return (False_ind (x = y) f = False_ind (x = y) (Hneq v))
            with
            end
          end in
    let nu_inv := fun (y : A) (v : x = y) => comp x x y (nu x eq_refl) v
    in
    let trans_sym_eq := fun (x y : A) (u : x = y) =>
        match u as e in (_ = y0) return (comp x y0 y0 e e = eq_refl) with
        | eq_refl => eq_refl
        end
    in
    let nu_left_inv_on := fun (y : A) (u : x = y) =>
        match u as e in (_ = y0) return (nu_inv y0 (nu y0 e) = e) with
        | eq_refl => trans_sym_eq _ _ (nu _ eq_refl)
        end in
    fun (y : A) (p1 p2 : x = y) =>
      eq_ind (nu_inv y (nu y p1)) (fun p3 : x = y => p3 = p2)
             (eq_ind (nu_inv y (nu y p2)) (fun p3 : x = y => nu_inv y (nu y p1) = p3)
                     (eq_ind (nu y p1) (fun e : x = y => nu_inv y (nu y p1) = nu_inv y e)
                             eq_refl (nu y p2) (nu_constant y p1 p2)) p2
                     (nu_left_inv_on _ p2)) p1 (nu_left_inv_on _ p1).

  Definition uip_trans (dec : forall x y : A, {x = y} + {x <> y})
  := @uip_prop_trans (fun a b => match dec a b with
                                 | left pf => or_introl pf
                                 | right pf' => or_intror pf'
                                 end).
End uip_trans.