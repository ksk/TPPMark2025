(* Solution to TPPMark 2025 *)
From mathcomp Require Import all_ssreflect.
From HB Require Import structures.
Parameter (n : nat) (pos_n : 0 < n).

Notation "f =3 g" := (forall x y z, f x y z = g x y z) (at level 70).
Lemma xorbA : associative xorb. Proof. by case; case; case. Qed.

Lemma filter_enum1 [T : finType] {p : T -> bool} (a : T) (q : T -> bool) :
  (forall x, p x = (x == a) && q x) ->
  filter p (enum T) = if q a then [:: a] else [::].
Proof.
  move=> H; case pa: (p a).
  - have p1: p =1 pred1 a
      by move=> x; apply /idP/idP=> [|/eqP->//]; rewrite H=> /andP[/eqP->]/=.
    by rewrite (eq_filter p1) filter_pred1_uniq ?enum_uniq ?mem_enum //;
    move: H pa=> ->/andP[_->].
  - have p0: p =1 pred0
      by move=> x; apply /negP=> /[dup]; rewrite {1}H=> /andP[/eqP->_]; 
      rewrite pa.
    by rewrite (eq_filter p0) filter_pred0; move: H pa=> ->;
    rewrite eq_refl=> /=->.
Qed.

Section Ordinal3.
  Definition o3_all (p : 'I_n -> 'I_n -> 'I_n -> bool) : bool :=
    all (fun x => all (fun y => all (fun z => p x y z) 
                                  (enum 'I_n)) (enum 'I_n)) (enum 'I_n).
  
  Lemma o3_allP (p : 'I_n -> 'I_n -> 'I_n -> bool) :
    reflect (forall x y z, p x y z) (o3_all p).
  Proof.
    apply (iffP allP).
    - by move=> /=H x y z; move: (H x); rewrite mem_enum=> /(_ isT)/allP/(_ y);
      rewrite mem_enum=> /(_ isT)/allP/(_ z); rewrite mem_enum=> /(_ isT).
    - by move=> H/=x _; apply /allP=> /=y _; apply /allP=> /=z _.
  Qed.
End Ordinal3.

Section Cube.
  (* Definition of lamp cube *)
  Definition cube := {ffun 'I_n -> {ffun 'I_n -> {ffun 'I_n -> bool}}}.

  (* Definition of all-lamp-off state *)
  Definition all_off (C : cube) : bool := o3_all (fun x y z => ~~ C x y z).
End Cube.

Section Actions.
  (* Definition of lamp toggle operation *)
  Inductive switch := SwX of 'I_n & 'I_n | SwY of 'I_n & 'I_n | SwZ of 'I_n & 'I_n.

  Definition eq_switch (s1 s2 : switch) : bool :=
    match s1, s2 with
    | SwX py1 pz1, SwX py2 pz2 => (py1 == py2) && (pz1 == pz2)
    | SwY px1 pz1, SwY px2 pz2 => (px1 == px2) && (pz1 == pz2)
    | SwZ px1 py1, SwZ px2 py2 => (px1 == px2) && (py1 == py2)
    | _, _ => false
    end.
  Lemma eq_switchP (sw1 sw2 : switch) : reflect (sw1 = sw2) (eq_switch sw1 sw2).
  Proof.
    apply (iffP idP); case: sw1=> ??; case: sw2=> ??//=.
    1, 2, 3: by move=> /andP[/eqP->/eqP->].
    all: by move=> [->->]; rewrite !eq_refl.
  Qed.
  HB.instance Definition _ := hasDecEq.Build switch eq_switchP.

  Definition act1 (sw : switch) (x y z : 'I_n) (b : bool) : bool :=
    match sw with
    | SwX py pz => if (y == py) && (z == pz) then ~~ b else b
    | SwY px pz => if (x == px) && (z == pz) then ~~ b else b
    | SwZ px py => if (x == px) && (y == py) then ~~ b else b
    end.

  Definition act1s (sws : seq switch) (x y z : 'I_n) (b : bool) : bool :=
    foldr (fun sw => act1 sw x y z) b sws.

  Lemma act1s_filter (sws : seq switch) x y z :
    act1s sws x y z =1 
    act1s [seq sw <- sws 
          | [|| sw == SwX y z, sw == SwY x z | sw == SwZ x y]] x y z.
  Proof.
    by elim: sws=> [|sw sws IH] b//=; rewrite fun_if !if_arg /= -IH fun_if;
    case: sw=> ??/=; do 3 case: eqP=> //=; move=> <-<-.
  Qed.

  Definition act (sw : switch) (C : cube) : cube :=
    [ffun x => [ffun y => [ffun z => act1 sw x y z (C x y z)]]].
  
  Definition acts (sws : seq switch) (C : cube) : cube := foldr act C sws.
  
  Lemma acts_act1s (sws : seq switch) (C : cube) x y z :
    acts sws C x y z = act1s sws x y z (C x y z).
  Proof. by elim: sws=> [|sw sws IH]//=; rewrite -IH/act !ffunE. Qed.
  
  Lemma acts_cat (sws1 sws2 : seq switch) (C : cube) :
    acts (sws1 ++ sws2) C = acts sws1 (acts sws2 C).
  Proof. by elim: sws1 C=> [|sw sws1 IH] C//=; rewrite IH. Qed.
End Actions.

Section Invariant.

  Definition o : 'I_n := Ordinal pos_n.

  Definition even_on (C : cube) (x y z : 'I_n) : bool :=
    foldl xorb true
      [:: C o o o; C x o o; C o y o; C o o z; C x y o; C x o z; C o y z; C x y z ].
  
  Definition valid (C : cube) :=
    o3_all (fun x y z => [|| x == o, y == o, z == o | even_on C x y z]).
  
  Lemma all_off_valid (C : cube) : all_off C -> valid C.
  Proof.
    by move=> /o3_allP/(fun H x y z => negbTE (H x y z))=> H;
    apply /o3_allP=> x y z; rewrite /even_on !H //= !orbT.
  Qed.

  Lemma even_on_act (sw : switch) (C : cube) x y z :
    even_on (act sw C) x y z = even_on C x y z.
  Proof.
    by rewrite /act/act1/even_on!ffunE; case: sw=> ??; 
    do 4 case: eqP=> //=; do 8 case: (C _ _ _).
  Qed.

  Lemma valid_act (sw : switch) (C : cube) : valid (act sw C) = valid C.
  Proof. by do 3 apply: eq_all=> ?; rewrite even_on_act. Qed.
End Invariant.

Section Solution.
  Definition ord_pairs := enum (('I_n * 'I_n)%type : finType).

  (* 3-step switch sequences to turn off all lamps *)
  Definition off_Xs (C : cube) : seq switch :=
    [seq SwX y z | '(y, z) <- ord_pairs & C o y z ]. 

  Definition off_Ys (C : cube) : seq switch :=
    [seq SwY x z | '(x, z) <- ord_pairs 
                 & (x != o) && acts (off_Xs C) C x o z].

  Definition off_Zs (C : cube) : seq switch :=
    [seq SwZ x y | '(x, y) <- ord_pairs 
                 & [&& x != o, y != o & acts (off_Ys C ++ off_Xs C) C x y o]].

  Lemma after_off_Xs (C : cube) (x y z : 'I_n) :
    acts (off_Xs C) C x y z = (x != o) && xorb (C x y z) (C o y z).
  Proof.
    rewrite acts_act1s act1s_filter /off_Xs filter_map/preim/=
      -filter_predI/predI/= (filter_enum1 (y, z) (fun '(y, z) => C o y z))/=;
    last by move=> [y' z']/=; rewrite /eq_op/=orbF.
    rewrite !fun_if !if_arg/= !eq_refl; 
    repeat case: eqP=> /=[->|]//=; do 2 case: (C _ _ _)=> //=.
  Qed.

  Lemma after_off_Ys (C : cube) (x y z : 'I_n) :
    acts (off_Ys C ++ off_Xs C) C x y z =
      [&& x != o, y != o & 
          foldr xorb false [:: C x y z; C o y z; C x o z; C o o z]].
  Proof.
    rewrite acts_cat acts_act1s after_off_Xs act1s_filter /off_Ys 
      filter_map/preim/= -filter_predI/predI/=
      (filter_enum1 (x, z) 
         (fun '(x, z) => (x != o) && acts (off_Xs C) C x o z) )/=;
    last by move=> [x' z']/=; rewrite /eq_op/=orbF.
    by rewrite !fun_if !if_arg/= after_off_Xs !eq_refl; 
    repeat case: eqP=> [->|]//=; do 4 case: (C _ _ _)=> //=.
  Qed.
    
  Lemma after_off_Zs (C : cube) (x y z : 'I_n) :
    acts (off_Zs C ++ off_Ys C ++ off_Xs C) C x y z =
      [&& x != o, y != o, z != o & 
          foldr xorb false [:: C x y z; C o y z; C x o z; C o o z; 
                               C x y o; C o y o; C x o o; C o o o]].
  Proof.
    rewrite acts_cat acts_act1s after_off_Ys act1s_filter /off_Zs
      filter_map/preim/= /(@eq_op switch)/= -filter_predI/predI/=
      (filter_enum1 (x, y)
         (fun '(x, y) => [&& x != o, y != o & 
                             acts (off_Ys C ++ off_Xs C) C x y o]))/=;
    last by move=> [x' y']/=; rewrite /(@eq_op (prod _ _))/=.
    by rewrite 2!fun_if !if_arg/= after_off_Ys !eq_refl/=;
    repeat case: eqP=> [->|]//=; do 8 case: (C _ _ _)=> //=.
  Qed.
End Solution.

Theorem tppmark2025 (C : cube) :
  valid C <-> exists sws, all_off (acts sws C).
Proof.
  split.
  - by exists(off_Zs C ++ off_Ys C ++ off_Xs C); apply /o3_allP=> x y z;
    rewrite after_off_Zs; move: H=> /o3_allP/(_ x y z); rewrite /even_on;
    do 3 case: eqP=> //=_; do 8 case: (C _ _ _)=> //.
  - case=> [sws]; move: sws C; apply: last_ind=> //=[|sws sw IH] C.
    + by apply: all_off_valid.
    + by rewrite -cats1 acts_cat=> /IH/=; rewrite valid_act.
Qed.
