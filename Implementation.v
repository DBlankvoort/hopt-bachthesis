From HoTT Require Import Basics Types.

Context `{Univalence}.



(* Before we do anything, let's redefine the integers to make them easier to work with. *)
Inductive Pos : Type :=
| one : Pos
| succ : Pos -> Pos.

Fixpoint pos_add (x y : Pos) : Pos :=
match x, y with
| one, one => succ one
| succ p, one => succ (succ p)
| one, succ q => succ (succ q)
| succ p, succ q => succ (succ (pos_add p q))
end.

Proposition pos_add_comm : forall (x y : Pos), pos_add x y = pos_add y x.
Proof.
induction x, y.
- reflexivity.
- reflexivity.
- reflexivity.
- cbn.
  exact (ap (succ o succ) (IHx y)).
Defined.



Inductive Int : Type :=
| zero : Int
| pos : Pos -> Int
| neg : Pos -> Int.

Definition int_succ (i : Int) : Int :=
match i with
| zero => pos one
| pos p => pos (succ p)
| neg p => match p with
             | one => zero
             | succ q => neg q
             end
end.

Definition int_pred (i : Int) : Int :=
match i with
| zero => neg one
| pos p => match p with
             | one => zero
             | succ q => pos q
             end
| neg p => neg (succ p)
end.

Lemma int_succ_pred : int_succ o int_pred == idmap.
Proof.
intro x.
induction x.
- reflexivity.
- induction p.
  + reflexivity.
  + reflexivity.
- induction p.
  + reflexivity.
  + reflexivity.
Defined.

Lemma int_pred_succ : int_pred o int_succ == idmap.
Proof.
intro x.
induction x.
- reflexivity.
- induction p.
  + reflexivity.
  + reflexivity.
- induction p.
  + reflexivity.
  + reflexivity.
Defined.

Definition equiv_int_succ : Equiv Int Int.
Proof.
simple refine (Build_Equiv _ _ _ _).
- apply int_succ.
- simple refine (isequiv_adjointify _ _ _ _).
  + exact int_pred.
  + exact int_succ_pred.
  + exact int_pred_succ.
Defined.

Fixpoint int_pos_sub (x y : Pos) : Int :=
match x, y with
| one, one => zero
| succ p, one => pos p
| one, succ q => neg q
| succ p, succ q => int_pos_sub p q
end.

Definition int_add (x y : Int) : Int :=
match x, y with
| zero, y => y
| x, zero => x
| pos p, pos q => pos (pos_add p q)
| neg p, neg q => neg (pos_add p q)
| pos p, neg q => int_pos_sub p q
| neg p, pos q => int_pos_sub q p
end.

Proposition int_add_comm : forall (x y : Int), int_add x y = int_add y x.
Proof.
induction x as [ |p1|p1], y as [ |p2|p2].
- reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- cbn.
  exact (ap pos (pos_add_comm p1 p2)).
- reflexivity.
- reflexivity.
- reflexivity.
- cbn.
  exact (ap neg (pos_add_comm p1 p2)).
Defined.





Fixpoint code_Pos (x y : Pos) : Type :=
match x, y with
| one, one => Unit
| succ _, one => Empty
| one, succ _ => Empty
| succ p, succ q => code_Pos p q
end.

Definition encode_pos (x y : Pos) (p : x = y) : code_Pos x y.
Proof.
induction p.
induction x.
- exact tt.
- cbn.
  exact IHx.
Defined.

Definition decode_pos : forall (x y : Pos), code_Pos x y -> (x = y).
Proof.
induction x, y.
- intro c.
  reflexivity.
- intro c.
  induction c.
- intro c.
  induction c.
- intro c.
  cbn in c. 
  pose (IHx y c) as p.
  exact (ap succ p). 
Defined.

Lemma encode_decode_pos (x y : Pos) : decode_pos x y o encode_pos x y == idmap.
Proof.
intro p.
induction p.
induction x.
- reflexivity.
- simpl.
  exact (ap (ap succ) IHx).
Defined.

Global Instance IsHProp_code_pos : forall (x y : Pos), IsHProp (code_Pos x y).
Proof.
induction x, y; apply _.
Defined.

Lemma decode_encode_pos : forall (x y : Pos), encode_pos x y o decode_pos x y == idmap.
Proof.
intros x y p.
apply path_ishprop.
Defined.

Definition equiv_Pos_encode {x y : Pos} : Equiv (code_Pos x y) (x = y).
Proof.
simple refine (Build_Equiv _ _ _ _).
2: simple refine (isequiv_adjointify _ _ _ _).
- apply decode_pos.
- apply encode_pos.
- apply encode_decode_pos.
- apply decode_encode_pos.
Defined.

Global Instance hset_pos : IsHSet Pos.
Proof.
intros x y. refine Trunc_is_trunc.
simple refine (istrunc_equiv_istrunc _ _).
- apply (code_Pos x y).
- apply equiv_Pos_encode.
- apply _. (* Finds IsHProp_code_pos *)
Defined.



Definition code_Int (x y : Int) : Type :=
match x, y with
| zero, zero => Unit
| zero, pos _ => Empty
| zero, neg _ => Empty
| pos _, zero => Empty
| pos p, pos q => code_Pos p q
| pos _, neg _ => Empty
| neg _, zero => Empty
| neg _, pos _ => Empty
| neg p, neg q => code_Pos p q
end.

Definition encode_int_refl (x : Int) : code_Int x x :=
match x with
| zero => tt
| (pos p) => encode_pos p p 1
| (neg p) => encode_pos p p 1
end.

Definition encode_int (x y : Int) (p : x = y) : code_Int x y.
Proof.
induction p.
apply encode_int_refl.
Defined.

Definition decode_int : forall (x y : Int), code_Int x y -> (x = y).
Proof.
induction x as [ |p1|p1], y as [ |p2|p2]; intro c.
- exact 1.
- induction c.
- induction c.
- induction c.
- cbn in c.
  pose (decode_pos p1 p2 c) as p. 
  exact (ap pos p).
- induction c.
- induction c.
- induction c.
- cbn in c. 
  pose (decode_pos p1 p2 c) as p. 
  exact (ap neg p).
Defined.

Lemma pos_succ_change (x y : Pos) (p : x = y) : ap pos (ap succ p) = ap int_succ (ap pos p).
Proof.
induction p.
reflexivity.
Defined.

Lemma neg_pred_change (x y : Pos) (p : x = y) : ap neg (ap succ p) = ap int_pred (ap neg p).
Proof.
induction p.
reflexivity.
Defined.



Lemma encode_decode_int (x y : Int) : decode_int x y o encode_int x y == idmap.
Proof.
intro p.
induction p.
induction x.
- reflexivity.
- cbn -[encode_int_refl].
  induction p.
  + reflexivity.
  + simpl.
    rewrite pos_succ_change.
    exact (ap (ap int_succ) IHp).
- cbn.
  induction p.
  + reflexivity.
  + simpl.
    rewrite neg_pred_change.
    exact (ap (ap int_pred) IHp).
Defined.

Lemma encode_int_pos {x y : Pos} {p : x = y}
  : encode_int (pos x) (pos y) (ap pos p) = encode_pos x y p.
Proof.
induction p.
reflexivity.
Defined.

Lemma encode_int_neg {x y : Pos} {p : x = y}
  : encode_int (neg x) (neg y) (ap neg p) = encode_pos x y p.
Proof.
induction p.
reflexivity.
Defined.

Lemma decode_encode_int (x y : Int) : encode_int x y o decode_int x y == idmap.
Proof.
induction x as [ |p1|p1], y as [ |p2|p2]; intro c.
- cbn in c; cbn.
  induction c.
  reflexivity.
- induction c.
- induction c.
- induction c.
- cbn in c; cbn.
  rewrite encode_int_pos.
  apply decode_encode_pos.
- induction c.
- induction c.
- induction c.
- cbn in c; cbn.
  rewrite encode_int_neg.
  apply decode_encode_pos.
Defined.

Definition equiv_Int_encode {x y : Int} : Equiv (code_Int x y) (x = y).
Proof.
simple refine (Build_Equiv _ _ _ _).
2: simple refine (isequiv_adjointify _ _ _ _).
- apply decode_int.
- apply encode_int.
- apply encode_decode_int.
- apply decode_encode_int.
Defined.

Global Instance IsHProp_code_int : forall (x y : Int), IsHProp (code_Int x y).
Proof.
induction x, y; apply _.
Defined.

Global Instance hset_int : IsHSet Int.
Proof.
intros x y; refine Trunc_is_trunc.
simple refine (istrunc_equiv_istrunc _ _).
- apply (code_Int x y).
- apply equiv_Int_encode.
- apply IsHProp_code_int.
Defined.





(* Now we create the HIT PT1 to represent the elementary path theory. *)
Module Export PT1.
Private Inductive PT1 : Type :=
| num : PT1.
Axiom add1 : num = num.

Definition PT1_rec {A : Type} (a : A) (p : a = a) (x : PT1) : A :=
match x with
| num => a
end.
Axiom PT1_rec_add1 : forall {A : Type} (a : A) (p : a = a), ap (PT1_rec a p) add1 = p.

Definition PT1_ind (P : PT1 -> Type) (b : P num) (l : add1 # b = b) (x : PT1) : P x :=
match x with
| num => b
end.
Axiom PT1_ind_add1 : forall (P : PT1 -> Type) (b : P num) (l : add1 # b = b), apD (PT1_ind P b l) add1 = l.
End PT1.

(* With this can define the corresponding interpreter for integers. *)
Definition I : PT1 -> Type.
Proof.
simple refine (PT1_rec _ _).
- exact Int.
- exact (path_universe_uncurried equiv_int_succ).
Defined.
Definition interp : (num = num) -> (Int <~> Int) :=
fun patch => equiv_path Int Int (ap I patch).



(* Let's see if the model works appropriately by proving some properties. *)
Proposition addsucc : interp add1 = equiv_int_succ.
Proof.
apply path_equiv.
funext x.
cbn.
rewrite PT1_rec_add1.
exact (transport_path_universe_uncurried equiv_int_succ x).
Defined.

Lemma interp_inverse (p : num = num) : interp p^ = equiv_inverse (interp p).
Proof.
unfold interp.
rewrite <- inverse_ap.
apply equiv_path_V.
Defined.

(* We will also need this one for later. *)
Proposition addVsucc : interp (add1^) = (equiv_inverse equiv_int_succ).
Proof.
rewrite (interp_inverse add1).
exact (ap equiv_inverse addsucc).
Defined.

(* oE is defined the other way around from in the paper so we have to switch around the terms.
   The point of the proof still stands though. *)
Proposition intcomp (p q : num = num) : interp (q @ p) = (interp p) oE (interp q).
Proof.
unfold interp.
rewrite (ap_pp I q p).
exact (equiv_path_pp (ap I q) (ap I p)).
Defined.

Proposition intzero : interp (add1 @ add1^) zero = zero.
Proof.
rewrite concat_pV.
reflexivity.
Defined.



(* Besides integers we will also want to prove for Booleans. *)
Definition I' : PT1 -> Type.
Proof.
simple refine (PT1_rec _ _).
- exact Bool.
- exact (path_universe_uncurried equiv_negb).
Defined.
Definition interp' : (num = num) -> (Bool <~> Bool) :=
fun patch => equiv_path Bool Bool (ap I' patch).


(* As a helper for the property to come, we will show here
   that a double negation of the booleans is equal to identity. *)
Lemma equivs_cancel : (equiv_negb oE equiv_negb) == 1%equiv.
Proof.
intros [ | ]. 
- reflexivity.
- reflexivity.
Defined.

(* Let's now show that the property posed in the paper holds in the correct way. *)
Proposition boolrefl1 : (ap I' add1) @ (ap I' add1) = 1.
Proof.
rewrite PT1_rec_add1.
rewrite <- (path_universe_compose_uncurried equiv_negb equiv_negb).
replace (path_universe_uncurried (equiv_compose equiv_negb equiv_negb)) with (path_universe (equiv_compose equiv_negb equiv_negb)).
2: reflexivity.
rewrite (path2_universe equivs_cancel).
apply path_universe_1.
Defined.



(* Now's the tricky part, let's try to implement merge. *)
Definition merge : (num = num) * (num = num) -> (num = num) * (num = num) :=
fun start => (snd start, fst start)
.

Lemma pairs_equal {A B : Type} (x y : A * B) (pxy : x = y) : (fst x = fst y) * (snd x = snd y).
Proof.
split.
- exact (ap fst pxy).
- exact (ap snd pxy).
Defined.



(* In order to prove reconcile we should apply the encode-repeat method, for
   which we need quite a bit of boilerplate. *)
Definition encode {x : PT1} : (num = x) -> (I x) :=
fun p => transport I p zero
.

Fixpoint looppow_pos (p : Pos) : (num = num) :=
match p with
| one => add1
| (succ p) => (looppow_pos p) @ add1
end.

Lemma looppow_pos_comm_add1 (p : Pos) : add1 @ (looppow_pos p) = (looppow_pos p) @ add1.
Proof.
induction p.
- reflexivity.
- enough (add1 @ ((looppow_pos p) @ add1) = (looppow_pos p) @ add1 @ add1). 1: exact X.
  rewrite concat_p_pp.
  refine (ap (fun z => z @ add1) _).
  exact IHp.
Defined.

Definition looppow (i : Int) : (num = num) :=
match i with
| zero => 1
| pos p => looppow_pos p
| neg p => (looppow_pos p)^
end.

Lemma looppow_comm_add1 (p : Pos) : add1 @ (looppow (pos p)) = (looppow (pos p)) @ add1.
Proof.
cbn -[looppow_pos].
exact (looppow_pos_comm_add1 p).
Defined.

Definition decode {x : PT1} : (I x) -> (num = x).
Proof.
revert x.
simple refine (PT1_ind _ _ _).
- cbn.
  exact looppow.
- funext i.
  cbn in i. 
  rewrite transport_arrow.
  rewrite transport_paths_r.
  rewrite transport_idmap_ap.
  replace (ap I add1^) with (path_universe_uncurried (equiv_path Int Int (ap I add1^))). 2: apply path_universe_uncurried_equiv_path.
  replace (equiv_path Int Int (ap I add1^)) with (equiv_inverse equiv_int_succ). 2: symmetry; apply addVsucc.
  rewrite path_universe_V_uncurried.
  rewrite transport_path_universe_V_uncurried.
  cbn.
  induction i; cbn.
  + apply concat_Vp.
  + induction p; cbn.
    -- apply concat_1p.
    -- reflexivity.
  + induction p; cbn.
    -- rewrite inv_pp.
       rewrite concat_pp_p.
       rewrite concat_Vp.
       rewrite concat_p1.
       reflexivity.
    -- enough (((add1 @ (looppow_pos p)) @ add1)^ @ add1 = (looppow_pos p @ add1)^). 1: rewrite looppow_comm_add1 in X; exact X.
       rewrite !inv_pp.
       rewrite concat_pp_p.
       refine (ap (fun z => add1^ @ z) _).
       rewrite concat_pp_p.
       rewrite concat_Vp.
       apply concat_p1.
Defined.

Proposition decode_encode (x : PT1) (p : num = x) : decode (encode p) = p.
Proof.
induction p.
reflexivity.
Defined.

Proposition encode_decode : forall (x : PT1) (c : I x), encode (decode c) = c.
Proof.
simple refine (PT1_ind (fun x => forall c : I x, encode (decode c) = c) _ _).
- intro c.
  induction c.
  1: reflexivity.
  1: induction p.
  3: induction p.
  + unfold encode.
    rewrite transport_idmap_ap.
    rewrite PT1_rec_add1.
    apply transport_path_universe_uncurried.
  + cbn.
    unfold encode.
    rewrite transport_idmap_ap.
    rewrite ap_pp.
    rewrite transport_pp.
    rewrite PT1_rec_add1.
    rewrite (transport_path_universe_uncurried equiv_int_succ _).
    rewrite <- transport_idmap_ap.
    unfold encode in IHp; rewrite IHp.
    reflexivity.
  + unfold encode.
    rewrite transport_idmap_ap.
    rewrite ap_V.
    rewrite PT1_rec_add1.
    apply transport_path_universe_V_uncurried.
  + cbn in IHp; unfold encode in IHp.
    cbn.
    rewrite <- looppow_comm_add1.
    rewrite inv_pp.
    unfold encode.
    rewrite transport_idmap_ap.
    rewrite !ap_pp.
    rewrite !transport_pp.
    rewrite !ap_V.
    rewrite PT1_rec_add1.
    rewrite (transport_path_universe_V_uncurried equiv_int_succ _).
    rewrite <- ap_V.
    rewrite <- transport_idmap_ap.
    rewrite IHp.
    reflexivity.
- apply path_ishprop.
Defined.

Lemma concat_to_pos_add : forall (p1 p2 : Pos), looppow_pos p1 @ looppow_pos p2 = looppow_pos (pos_add p1 p2).
Proof.
induction p1, p2; cbn.
- reflexivity.
- rewrite concat_p_pp.
  rewrite looppow_pos_comm_add1.
  reflexivity.
- reflexivity.
- rewrite concat_p_pp.
  refine (ap (fun z => z @ add1) _).
  rewrite concat_pp_p.
  rewrite looppow_pos_comm_add1.
  rewrite concat_p_pp.
  exact (ap (fun z => z @ add1) (IHp1 p2)).
Defined.

Lemma concat_to_pos_sub : forall p1 p2 : Pos, looppow_pos p1 @ (looppow_pos p2)^ = looppow (int_pos_sub p1 p2).
Proof.
induction p1, p2; cbn.
- apply concat_pV.
- rewrite inv_pp.
  rewrite concat_p_pp.
  rewrite concat_pV.
  apply concat_1p.
- apply concat_pp_V.
- rewrite inv_pp.
  rewrite concat_p_pp.
  rewrite concat_pp_V.
  apply IHp1.
Defined.

Lemma looppow_pos_pV_comm : forall p1 p2 : Pos, (looppow_pos p2)^ @ (looppow_pos p1) = (looppow_pos p1) @ (looppow_pos p2)^.
Proof.
induction p1, p2; cbn.
- rewrite concat_pV.
  apply concat_Vp.
- replace ((looppow_pos p2 @ add1)^ @ add1) with ((add1 @ looppow_pos p2)^ @ add1). 2: rewrite looppow_pos_comm_add1; reflexivity.
  rewrite !inv_pp.
  rewrite concat_p_Vp.
  apply concat_pV_p.
- replace (add1^ @ (looppow_pos p1 @ add1)) with (add1^ @ (add1 @ looppow_pos p1)). 2: rewrite looppow_pos_comm_add1; reflexivity.
  rewrite concat_pp_V.
  apply concat_V_pp.
- replace ((looppow_pos p2 @ add1)^ @ (looppow_pos p1 @ add1)) with ((add1 @ looppow_pos p2)^ @ (looppow_pos p1 @ add1)). 2: rewrite looppow_pos_comm_add1; reflexivity.
  rewrite !inv_pp.
  rewrite <- looppow_pos_comm_add1.
  rewrite concat_p_pp.
  rewrite concat_pV_p.
  rewrite looppow_pos_comm_add1.
  rewrite concat_pp_p.
  rewrite concat_p_Vp.
  apply IHp1.
Defined.

Lemma ctpa_pos_pos : forall (p1 p2 : Pos), looppow (pos p1) @ looppow (pos p2) = looppow (pos (pos_add p1 p2)).
Proof.
cbn.
exact concat_to_pos_add.
Defined.

Lemma ctpa_neg_neg : forall (p1 p2 : Pos), looppow (neg p1) @ looppow (neg p2) = looppow (neg (pos_add p1 p2)).
Proof.
cbn.
intros p1 p2.
rewrite <- inv_pp.
rewrite pos_add_comm.
exact (ap inverse (concat_to_pos_add p2 p1)).
Defined.

Lemma ctpa_pos_neg : forall (p1 p2 : Pos), looppow (pos p1) @ looppow (neg p2) = looppow (int_pos_sub p1 p2).
Proof.
cbn.
exact concat_to_pos_sub.
Defined.

Lemma ctpa_neg_pos : forall (p1 p2 : Pos), looppow (neg p1) @ looppow (pos p2) = looppow (int_pos_sub p2 p1).
Proof.
cbn.
intros p1 p2.
rewrite looppow_pos_pV_comm.
apply concat_to_pos_sub.
Defined.



Lemma concat_to_add_looppow (n m : I num) : looppow n @ looppow m = looppow (int_add n m).
Proof.
induction n as [ |p1|p1], m as [ |p2|p2]; cbn -[looppow].
- reflexivity.
- apply concat_1p.
- apply concat_1p.
- apply concat_p1.
- apply ctpa_pos_pos.
- apply ctpa_pos_neg.
- apply concat_p1.
- apply ctpa_neg_pos.
- apply ctpa_neg_neg.
Defined.

Lemma concat_to_add (n m : I num) : (decode n) @ (decode m) = decode (int_add n m : I num).
Proof.
apply concat_to_add_looppow.
Qed.




Global Instance equiv_encode (x : PT1) : @IsEquiv (num = x) (I x) encode.
Proof.
simple refine (isequiv_adjointify _ _ _ _).
- exact decode.
- cbn. 
  intro x0. 
  apply encode_decode.
- cbn. 
  intro x0. 
  apply decode_encode.
Defined.

Global Instance equiv_decode (x : PT1) : @IsEquiv (I x) (num = x) decode.
Proof.
simple refine (isequiv_adjointify _ _ _ _).
- exact encode.
- cbn. 
  intro x0. 
  apply decode_encode.
- cbn. 
  intro x0. 
  apply encode_decode.
Defined.

Print equiv_inj.

Lemma encode_concat (f g : num = num) : encode (f @ g) = int_add (encode f) (encode g).
Proof.
apply (equiv_inj decode).
rewrite decode_encode.
rewrite <- concat_to_add.
rewrite !decode_encode.
reflexivity.
Defined.

(* With this we can prove the reconcile property. *)
Proposition reconcile (f1 f2 g1 g2 : num = num) (merger : (merge (f1, f2)) = (g1, g2)) : 
                                             (g1 @ f1) = (g2 @ f2).
Proof.
unfold merge in merger; cbn in merger.
apply pairs_equal in merger.
cbn in merger. 
destruct merger as (eq1 & eq2).
rewrite eq1.
rewrite eq2.
apply (equiv_inj encode).
rewrite !encode_concat.
apply int_add_comm.
Defined.

Definition symmetric (f1 f2 g1 g2 : num = num) (merger : merge (f1, f2) = (g1, g2)) : (merge (f2, f1) = (g2, g1)).
Proof.
unfold merge in merger; cbn in merger.
apply pairs_equal in merger.
cbn in merger. 
destruct merger as (eq1 & eq2).
rewrite eq1.
rewrite eq2.
reflexivity. 
Defined.