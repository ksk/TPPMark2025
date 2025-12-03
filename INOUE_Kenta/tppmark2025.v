From mathcomp
     Require Import all_ssreflect all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.

(* ********************* *)
Section Mulord.
  (* 'I_n * 'I_m <-> 'I_(n * m) *)

  Lemma mulord_subproof (n m:nat) (x:'I_n * 'I_m) : x.1 * m + x.2 < n * m.
  Proof.
    case : m x =>[|m][i j]/=; [by case : j|]. move : (ltn_ord i).
    rewrite -(leq_pmul2r (ltn0Sn m)) mulSn addnC. apply /leq_trans.
      by rewrite ltn_add2l ltn_ord.
  Qed.

  Definition mulord (n m:nat) (x:'I_n * 'I_m) : 'I_(n * m) :=
    Ordinal (mulord_subproof x).

  Lemma unmulordl_subproof (n m:nat) (x:'I_(n * m)) : x %/ m < n.
  Proof.
    case : m =>[|m] in x *; [by case : x => m; rewrite muln0|].
      by rewrite ltn_divLR.
  Qed.

  Lemma unmulordr_subproof (n m:nat) (x:'I_(n * m)) : x %% m < m.
  Proof.
    rewrite ltn_mod. case : m =>[|m]// in x *.
      by case : x => m; rewrite muln0.
  Qed.

  Definition unmulord (n m:nat) (x:'I_(n * m)) : 'I_n * 'I_m :=
    (Ordinal (unmulordl_subproof x), Ordinal (unmulordr_subproof x)).

  Lemma mulordK (n m:nat) : cancel (@mulord n m) (@unmulord _ _).
  Proof.
    rewrite /unmulord =>[[a b]]. apply /eqP/andP=>/=. split; apply /eqP/ord_inj.
    - case : m =>[|m]/= in b *; [by case : b|]. rewrite divnMDl //.
        by rewrite divn_small // addn0.
    - case : m =>[|m]/= in b *; [by case : b|]. rewrite modnMDl //.
        by rewrite modn_small //.
  Qed.

  Lemma unmulordK (n m:nat) : cancel (@unmulord n m) (@mulord _ _).
  Proof.
    move => x. apply /ord_inj. by rewrite /= -divn_eq.
  Qed.
End Mulord.

Section Exp2Vector.
  Variable (K:fieldType).
  (* K ^ n -> vectType K *)

  Definition exp2v (n:nat) (x:K ^ n) :
    exp_vectType (regular_vectType _) n := x.

  Lemma exp2v_inj (n:nat) : injective (@exp2v n).
  Proof. done. Qed.

  Lemma exp2v_additive (n:nat) : {morph (@exp2v n) : x y / (x + y)%R}.
  Proof. done. Qed.
End Exp2Vector.

Section Ffun0.
  Lemma eq_ffun0 (T:finType) (X:Type):
    #|T| = 0 -> forall f0:{ffun T -> X}, all_equal_to f0.
  Proof.
    move =>/card0_eq H f0 f. apply /ffunP => x. by move : (H x).
  Qed.
End Ffun0.

Section Vector.
  Variable (K:fieldType).
  Variable (vT:vectType K).
  Variable (I:eqType).

  Lemma sumv_sup_seq (r:seq I) (P:pred I) (U:{vspace vT}) Vs:
    {in r, forall i0, P i0 -> (U <= Vs i0)%VS ->
                      (U <= \sum_(i <- r | P i) Vs i)%VS}.
  Proof.
    move => i0. elim : r =>[|x r IH]//=.
    rewrite in_cons big_cons =>/orP[/eqP->-> HU|Hr Hi0].
    - exact /(subv_trans HU)/addvSl.
    - case : ifP =>_ HU; [apply /(subv_trans (IH _ _ _))=>//|exact /IH].
      exact /addvSr.
  Qed.

  Lemma subv_sum_seqP (r:seq I) (P:pred I) Us (V:{vspace vT}):
    reflect {in r, forall i, P i -> Us i <= V}%VS
            (\sum_(i <- r | P i) Us i <= V)%VS.
  Proof.
    apply /(iffP idP);
      elim : r =>[|x r IH]//=; rewrite ?big_nil ?big_cons ?sub0v //;
                          case : ifP => HPx; rewrite ?subv_add.
    - move =>/andP[Hx /IH H] y. rewrite in_cons =>/orP[/eqP->|]//. exact /H.
    - move =>/IH H y.
        by rewrite in_cons =>/orP[/eqP->|]; [rewrite HPx|exact /H].
    - move => H. rewrite (H _ (mem_head _ _) HPx). apply /IH => y Hy.
      apply /H. by rewrite in_cons Hy orbT.
    - move => H. apply IH => y Hy. apply /H. by rewrite in_cons Hy orbT.
  Qed.

  Lemma memv_sumr_seq (r:seq I) (P:pred I) (vs:I -> vT) (Us:I -> {vspace vT}):
    {in r, forall i, P i -> vs i \in Us i} ->
    (\sum_(i <- r | P i) vs i)%R \in (\sum_(i <- r | P i) Us i)%VS.
  Proof.
    elim : r =>[|i r IH]/=; [by rewrite !big_nil memv0|rewrite !big_cons => H].
      by case : ifP =>[/(H _ (mem_head _ _))/memv_add|_]; [apply|];
                        apply /IH => x Hx; apply /H; rewrite in_cons Hx orbT.
  Qed.

  Lemma sumvW (r:seq I) (P:pred I) (Us:I -> {vspace vT}):
    {in r, forall x, P x -> Us x <= \sum_(i <- r | P i) Us i}%VS.
  Proof.
    move => x. elim : r =>[|y r IH]//=.
    rewrite in_cons big_cons =>/orP[/eqP->->|Hr Hx]; [exact /addvSl|].
    case : ifP =>_; [|exact /IH]. rewrite -[Us x]add0v.
    exact /(addvS (sub0v _))/IH.
  Qed.

  Lemma myfreeP (r:seq vT):
    reflect (uniq r /\ {in r, forall v, v \notin <<[seq x <- r | x != v]>>%VS})
            (free r).
  Proof.
    apply /(iffP idP) =>[Hr|[]].
    - move : (free_uniq Hr) => Huniq. split =>// x Hx. rewrite -rem_filter //.
      move : Hr. by rewrite (perm_free (perm_to_rem Hx)) free_cons =>/andP[].
    - elim : r =>[|v r IH]/=; [by rewrite nil_free|]. rewrite free_cons.
      move =>/andP[Hvr Huniq] H. rewrite IH =>//[|x Hx].
      + move : (H _ (mem_head _ _)). rewrite eq_refl /=.
        have ->: [seq x <- r | x != v] = r =>[|->]//. apply /all_filterP/allP.
        move => x Hx. apply /negP =>/eqP Hxv. by move : Hxv Hx Hvr =>->->.
      + move : (H x). rewrite in_cons Hx orbT =>/(_ (erefl _)).
        case : ifP =>//_. rewrite span_cons => Hxv. apply /negP.
        move =>/(subvP (addvSr <[v]>%VS _)). exact /negP.
  Qed.

  Lemma free_catP (r s:seq vT):
    reflect [/\ uniq (r ++ s),
             {in s, forall v, v \notin <<r>> + <<[seq x <- s | x != v]>>}%VS &
             {in r, forall v, v \notin <<[seq x <- r | x != v]>> + <<s>>}%VS]
            (free (r ++ s)).
  Proof.
    apply /(iffP idP) =>[/myfreeP[Huniq H]|[Huniq Hs Hr]]; [|apply /myfreeP].
    - split =>// v Hv; move : (H v);
        rewrite mem_cat filter_cat Hv ?orbT =>/(_ (erefl _)).
      + move : Huniq. rewrite cat_uniq =>/and3P[_/hasPn/(_ _ Hv)/= Hvr _].
        suff ->: [seq x <- r | x != v] = r by rewrite span_cat.
        apply /all_filterP/allP => x Hx. apply /negP =>/eqP Hxv.
          by move : Hxv Hx Hvr =>->->.
      + move : Huniq. rewrite (perm_uniq (permEl (perm_catC _ _))) cat_uniq.
        move =>/and3P[_/hasPn/(_ _ Hv)/= Hvs _].
        suff ->: [seq x <- s | x != v] = s by rewrite span_cat.
        apply /all_filterP/allP => x Hx. apply /negP =>/eqP Hxv.
          by move : Hxv Hx Hvs =>->->.
    - split =>// v.
        by rewrite mem_cat filter_cat span_cat =>/orP[/Hr|/Hs]/negP H;
          apply /negP => Hv; apply /H; apply : subvP Hv; apply /addvS =>//;
          apply /sub_span/mem_subseq/filter_subseq.
  Qed.

  Lemma dim_free (r:seq vT): free r -> \dim <<r>>%VS = size r.
  Proof.
    rewrite free_directv =>/andP[H /directvP]/=. rewrite span_def =>->.
    rewrite (eq_big_seq (fun => 1)) ?sum1_size =>// i Hi. rewrite dim_vline.
    have ->//: (i != 0%R). apply /eqP => Hi0. by move : Hi0 Hi H =>->->.
  Qed.    
End Vector.


Section Tppmark.
  Definition hyperspace (s:seq nat) :=
    foldr (fun n T => prod_finType (ordinal_finType n) T) unit_finType s.
  (* foldr (prod \o ordinal) unit s *)

  Variable (K:fieldType).

  Definition state (s:seq nat) : Type := {ffun hyperspace s -> K}.
  Definition surface (s:seq nat) :=
    prod_finType (ordinal_finType (size s)) (hyperspace s).
(*  'I_(size s) * hyperspace s. *)

  Fixpoint switch_rec (s:seq nat) (n:nat) :
    hyperspace s -> state s -> state s :=
    match s,n return hyperspace s -> state s -> state s with
    | [::], _ => fun _ => id
    | _ :: s', 0 => fun c t =>
                      [ffun x => if (x.2 == c.2) then (t x + 1)%R else t x]
    | _ :: s', n'.+1 => fun c t =>
                          [ffun x =>
                           if x.1 == c.1
                           then switch_rec n' c.2 [ffun y => t (x.1,y)] x.2 
                           else t x]
    end.

  Definition switch (s:seq nat) (b:surface s) : state s -> state s :=
    switch_rec b.1 b.2.

  Definition execute (s:seq nat) (p:seq (surface s)) : state s -> state s :=
    foldr (comp \o @switch _) id p.

  Definition reachable (s:seq nat) (init:state s) : Prop :=
    exists p:seq (surface s), execute p init = [ffun => 0%R].


  Fixpoint surface2state_rec (s:seq nat) (n:nat) : hyperspace s -> state s :=
    match s,n return hyperspace s -> state s with
    | [::], _ => fun _ => [ffun => 0%R]
    | _ :: s', 0 => fun c => [ffun x => if (x.2 == c.2) then 1%R else 0%R]
    | _ :: s', n'.+1 => fun c =>
                          [ffun x => if (x.1 == c.1)
                                     then surface2state_rec n' c.2 x.2 else 0%R]
    end.

  Definition surface2state (s:seq nat) (c:surface s) : state s :=
    surface2state_rec c.1 c.2.


  (* hyperspace s <-> 'I_(foldr muln 1 s) *)
  Fixpoint hyperspace2ord (s:seq nat) : hyperspace s -> 'I_(foldr muln 1 s) :=
    match s return hyperspace s -> 'I_(foldr muln 1 s) with
    | [::] => fun => ord0
    | _ :: _ => fun x => mulord (x.1, hyperspace2ord x.2)
    end.

  Fixpoint ord2hyperspace (s:seq nat) : 'I_(foldr muln 1 s) -> hyperspace s :=
    match s return 'I_(foldr muln 1 s) -> hyperspace s with
    | [::] => fun => tt
    | _ :: _ => fun x => let: (x1, x2) := unmulord x in (x1, ord2hyperspace x2)
    end.

  Lemma hyperspace2ordK (s:seq nat) :
    cancel (@hyperspace2ord s) (@ord2hyperspace _).
  Proof.
    elim : s =>[|n s IH]/=[]// x1 x2.
    move : (mulordK (x1, hyperspace2ord x2)) =>[->->]. by rewrite IH.
  Qed.

  Lemma ord2hyperspaceK (s:seq nat) :
    cancel (@ord2hyperspace s) (@hyperspace2ord _).
  Proof.
    elim : s =>[|n s IH]/= x; [by rewrite !ord1|]. by rewrite IH unmulordK.
  Qed.

  (* state s <-> vectType K *)
  Definition state2vec (s:seq nat) (t:state s) :
    exp_vectType _ (foldr muln 1 s) := exp2v [ffun x => t (ord2hyperspace x)].

  Definition vec2state (s:seq nat)
             (v:exp_vectType (regular_vectType K) (foldr muln 1 s))
    : state s := [ffun x => v (hyperspace2ord x)].

  Lemma state2vecK (s:seq nat): cancel (@state2vec s) (@vec2state _).
  Proof.
    move => f. apply /ffunP => c. by rewrite !ffunE hyperspace2ordK.
  Qed.

  Lemma vec2stateK (s:seq nat): cancel (@vec2state s) (@state2vec _).
  Proof.
    move => f. apply /ffunP => c. by rewrite !ffunE ord2hyperspaceK.
  Qed.

  Notation surface2vec c := (state2vec (surface2state c)).

  Lemma state2vec_inj (s:seq nat): injective (@state2vec s).
  Proof.
    rewrite /state2vec => x y /exp2v_inj/ffunP H. apply /ffunP => c.
    move : (H (hyperspace2ord c)). by rewrite !ffunE hyperspace2ordK.
  Qed.

  Lemma state2vec0 (s:seq nat) : @state2vec s [ffun => 0%R] = 0%R.
  Proof. apply /ffunP => x. by rewrite !ffunE. Qed.

  Lemma state2vec_switch (s:seq nat) (c:surface s) (t:state s):
    state2vec (switch c t) = (state2vec t + state2vec (surface2state c))%R.
  Proof.
    case : c =>[k c]. rewrite /switch/surface2state/=/state2vec -exp2v_additive.
    congr(exp2v _). apply /ffunP => x. rewrite !ffunE.
    move : (nat_of_ord k) => n. elim : s {k} =>[|k s IH]/= in n t c x *.
    - by rewrite ffunE addr0.
    - by case : n =>[|n]; rewrite !ffunE;
                      case : ifP =>_//=; rewrite ?addr0 // IH ffunE.
  Qed.

  Lemma state2vec_execute (s:seq nat) (p:seq (surface s)) (init:state s):
    state2vec (execute p init) =
    (\sum_(c <- p) state2vec (surface2state c) + state2vec init)%R.
  Proof.
    elim : p =>[|c p IH]/=; [by rewrite big_nil add0r|].
      by rewrite state2vec_switch big_cons IH addrC addrA.
  Qed.


  Definition vreachable' (s:seq nat) (init:state s) :=
    exists (p:seq (surface s)),
      (\sum_(c <- p) surface2vec c + state2vec init)%R = 0%R.

  Lemma reachableP' (s:seq nat) (init:state s) :
    reachable init <-> vreachable' init.
  Proof.
    split =>[][p] H; exists p.
    - rewrite -state2vec_execute /state2vec.
      apply /ffunP => y. by rewrite H !ffunE.
    - apply /state2vec_inj. by rewrite state2vec_execute H state2vec0.
  Qed.


  (* K *)
  Definition cyclic_K := forall x:K, exists n, x = (n%:R)%R.
(* Hcyclic K <-> #| K | is prime i.e. K ~ F_p *)

  Definition vreachable (s:seq nat) (init:state s) :=
    state2vec init \in (\sum_(c in surface s) <[surface2vec c]>)%VS.

  Lemma vreachableP (s:seq nat) (init:state s):
    cyclic_K -> reflect (vreachable' init) (vreachable init).
  Proof.
    rewrite /vreachable -memvN => Hcyclic. apply /(iffP memv_sumP).
    - case => vs H =>/eqP. rewrite -big_enum -sub0r subr_eq eq_sym =>/eqP/=.
      rewrite /vreachable'.
      elim : (enum (surface s)) (state2vec init) =>[|c p IH] vinit.
      + move => Hinit. exists [::]. move : Hinit. by rewrite !big_nil.
      + rewrite big_cons. rewrite addrAC addrC =>/IH[q Hq].
        move : (H c (erefl _)) =>/vlineP[k]. case : (Hcyclic k) => nk ->.
        rewrite scaler_nat => Hvsc. exists (q ++ mkseq (fun _ => c) (nk - 0)).
          by rewrite big_cat big_map /= sumr_const_nat subn0 -Hvsc -addrA.
    - case => p /eqP. rewrite addr_eq0 =>/eqP<-.
      exists (fun c => state2vec (surface2state c) *+ count_mem c p)%R =>[c _|].
      + by rewrite -scaler_nat; apply /vlineP; exists ((count_mem c p)%:R)%R.
      + elim : p =>[|x p IH]/=.
        * by rewrite big_nil /= (eq_bigr (fun => 0%R)) // sumr_const mul0rn.
        * rewrite big_cons IH (bigD1 x) //= addrA.
          rewrite [(\sum_(i in surface s) surface2vec i *+ _)%R](bigD1 x) //=.
          rewrite eq_refl mulrS. congr(_ + _)%R. apply /eq_bigr => c.
            by rewrite eq_sym =>/negbTE->.
  Qed.

  Lemma reachableP (s:seq nat) (init:state s):
    cyclic_K -> reflect (reachable init) (vreachable init).
  Proof.
    move => Hcyclic.
      by apply /(iffP idP)
      =>[/(@vreachableP _ _ Hcyclic)/reachableP'|
         /reachableP'/(@vreachableP _ _ Hcyclic)].
  Qed.


  (* basis *)
  Fixpoint statebasis' (s:seq nat) : seq (state s) :=
        match s return seq (state s) with
    | [::] => [::]
    | n :: s' => codom (fun c => [ffun x => if x.2 == c then 1%R else 0%R])
                       ++ flatten
                       [seq map
                            (fun f:state s' =>
                               [ffun x => if val x.1 == i then f x.2 else 0%R])
                            (statebasis' s') | i <- iota 0 n]
        end.
  (* [seq [ffun x => if val x.1 == i then f x.2 else 0%R]
     | i <- iota 1 n, f <- statebasis' s']*)

  Lemma surface_statebasis' (s:seq nat) (c:surface s) :
    surface2state c \in statebasis' s.
  Proof.
    rewrite /surface2state.
    elim : s c =>[|n s IH]/=[i c]/=; [by case : i|].  rewrite mem_cat.
    elim : (val i) (ltn_ord i) =>[|j IHj]//=; rewrite ?ltnS => Hj; apply /orP.
    - left. apply /codomP. by exists c.2.
    - right. apply /allpairsP.
      exists (val c.1, surface2state (Ordinal Hj,c.2)). rewrite IH mem_iota.
        by rewrite add0n ltn_ord.
  Qed.

  Lemma statebasis'_surface (s:seq nat) (x:state s):
    x \in statebasis' s -> x = 0%R \/ exists c, x = surface2state c.
  Proof.
    elim : s x =>[|[|n] s IH]// x;
                   [by left; apply /eq_ffun0/eq_card0 =>[[[]]]|].
    rewrite mem_cat =>/orP[/codomP[h ->]|/allpairsP[[i y][]]].
    - right. exists (ord0, (ord0,h)). apply /ffunP => y. by rewrite !ffunE.
    - rewrite mem_iota add0n =>/= Hi /IH[->|[c ->]]->.
      + left. apply ffunP => z. rewrite !ffunE. by case : ifP.
      + right. exists (lift ord0 c.1, (Ordinal Hi,c.2)). apply /ffunP => z.
        by rewrite !ffunE.
  Qed.

  Lemma eq_surface_statebasis' (s:seq nat):
    (\sum_(c in surface s) <[surface2vec c]> =
     <<[seq state2vec x | x <- statebasis' s]>>)%VS.
  Proof.
    rewrite span_def big_map. apply /subv_anti/andP.
    split; [apply /subv_sumP => c _|].
    - exact /(sumv_sup_seq (surface_statebasis' c)).
    - apply /subv_sum_seqP => x /statebasis'_surface[->|[c ->]] _.
      + by rewrite state2vec0 sub0v.
      + exact : sumv_sup (subvv _).
  Qed.

  Fixpoint statebasis (s:seq nat) : seq (state s) :=
        match s return seq (state s) with
    | [::] => [::]
    | n :: s' => (if n is S _
                 then codom (fun c => [ffun x => if x.2 == c then 1%R else 0%R])
                 else [::])
                   ++ flatten
                   [seq map
                        (fun f:state s' =>
                           [ffun x => if val x.1 == i then f x.2 else 0%R])
                        (statebasis s') | i <- iota 0 n.-1]
        end.

  Notation basis s := [seq state2vec x | x <- statebasis s].

  Lemma le_statebasis_sub_lemma
        (n:nat) (s:seq nat) (sx sy:seq (state s)) (sn:seq nat):
    (\sum_(x <- sx) <[state2vec x]> <= \sum_(x <- sy) <[state2vec x]>)%VS ->
    (\sum_(x <- flatten
                  [seq map
                       (fun f:state s =>
                          [ffun x => if val x.1 == i then f x.2 else 0%R])
                       sx | i <- sn]) <[@state2vec (n :: s) x]> <=
     \sum_(x <- flatten
                  [seq map
                       (fun f:state s =>
                          [ffun x => if val x.1 == i then f x.2 else 0%R])
                       sy | i <- sn]) <[@state2vec (n :: s) x]>)%VS.
  Proof.
    move => H. elim : sn =>[|i sn IH]//=. rewrite !big_cat /= !big_map.
    apply /addvS =>//. apply /subv_sum_seqP => f Hf _.
    have : (<[state2vec f]> <= \sum_(x <- sx) <[state2vec x]>)%VS
      := sumv_sup_seq Hf (erefl _) (subvv _). rewrite -!memvE =>/(subvP H).
    elim : sy {H IH Hf} f =>[|g sy IH]/= f.
    - rewrite !big_nil !memv0 =>/eqP. rewrite -state2vec0 =>/state2vec_inj->.
      apply /eqP/ffunP => z. rewrite !ffunE. by case : ifP.
    - rewrite !big_cons =>/memv_addP/=[fg Hfg][vf].
      rewrite -[vf]vec2stateK -[fg]vec2stateK =>/IH Hvf H. apply /memv_addP.
      exists (@state2vec (n :: s)
                         [ffun x => if val x.1 == i
                                    then vec2state fg x.2 else 0%R]).
      + apply /vlineP. move : Hfg =>/vlineP[kg ->]. exists kg.
        apply /ffunP => c. rewrite !ffunE ord2hyperspaceK. case : ifP =>_//.
          by rewrite scaler0.
      + exists (@state2vec (n :: s)
                           [ffun x => if val x.1 == i
                                      then vec2state vf x.2 else 0%R]) =>//.
        apply /ffunP => c. rewrite !ffunE. case : ifP =>_; [|by rewrite addr0].
        move : H =>/ffunP=>/(_ (hyperspace2ord (@ord2hyperspace (n :: s) c).2)).
          by rewrite !ffunE !ord2hyperspaceK.
  Qed.

  Lemma eq_statebasis_sub_lemma
        (n:nat) (s:seq nat) (sx sy:seq (state s)) (sn:seq nat):
    (\sum_(x <- sx) <[state2vec x]> = \sum_(x <- sy) <[state2vec x]>)%VS ->
    (\sum_(x <- flatten
                  [seq map
                       (fun f:state s =>
                          [ffun x => if val x.1 == i then f x.2 else 0%R])
                       sx | i <- sn]) <[@state2vec (n :: s) x]> =
     \sum_(x <- flatten
                  [seq map
                       (fun f:state s =>
                          [ffun x => if val x.1 == i then f x.2 else 0%R])
                       sy | i <- sn]) <[@state2vec (n :: s) x]>)%VS.
  Proof.
    move => H. apply /subv_anti. by rewrite !le_statebasis_sub_lemma // H.
  Qed.


  Lemma eq_statebasis (s:seq nat):
    (<<[seq state2vec x | x <- statebasis' s]>> = <<basis s>>)%VS.
  Proof.
    rewrite !span_def !big_map. elim : s =>[|n s IH]//=.
    rewrite !big_cat !(eq_statebasis_sub_lemma _ _ IH).
    case : n
    =>[|n]; [rewrite !big_nil codomE big_map big1 // => i _; apply /subv_anti;
             rewrite sub0v andbT -memvE memv0; apply /eqP/ffunP => x;
             by case : (@ord2hyperspace (0 :: s) x).1|].
    rewrite -addn1 iotaD addn1 add0n map_cat flatten_cat /= cats0 big_cat.
    rewrite addvA /=. apply /addv_idPl/subv_sum_seqP =>/= f'.
    move =>/mapP[f Hf ->] _. rewrite -memvE. apply /memv_addP.
    exists (@state2vec (n.+1 :: s) [ffun x => f x.2]).
    - rewrite codomE big_map big_enum /=. apply /memv_sumP.
      exists (fun i => @state2vec (n.+1 :: s)
                                  [ffun x => if x.2 == i then f i else 0%R])
      =>[i _|]; [apply /vlineP|apply /ffunP => x; rewrite !ffunE].
      + exists (f i). apply /ffunP => x. rewrite !ffunE.
          by case : ifP =>_; rewrite ?scaler0 // /scale /= mulr1.
      + rewrite sum_ffunE (bigD1 (@ord2hyperspace (n.+1 :: s) x).2) //=.
        rewrite big1 ?addr0 =>/=[|i]; rewrite !ffunE /= ?eq_refl // eq_sym.
          by move =>/negbTE->.
    - exists (-\sum_(i <- iota 0 n)
               @state2vec (n.+1 :: s)
               [ffun x => if val x.1 == i then f x.2 else 0%R])%R.
      + rewrite big_flatten /= big_map memvN. apply /memv_sumr_seq => i Hi _.
        rewrite big_map memvE. exact /(sumv_sup_seq Hf (erefl _) (subvv _)).
      + apply /ffunP => x. rewrite !ffunE sum_ffunE. case : ifP =>[|/negbT] Hn.
        * rewrite big1_seq ?ffunE ?subr0 =>//= i. rewrite mem_iota /= !ffunE.
          rewrite add0n. case : ifP Hn =>// /eqP->/eqP->. by rewrite ltnn.
        * rewrite (bigD1_seq (val (@ord2hyperspace (n.+1 :: s) x).1));
            rewrite ?iota_uniq ?mem_iota // ?add0n ?ltn_neqAle ?Hn -1?ltnS;
            [|exact /(ltn_ord (@ord2hyperspace (n.+1 :: s) x).1)].
          rewrite big1_seq ?addr0 ?ffunE ?eq_refl /= ?addr0 ?subrr =>// i.
            by rewrite !ffunE eq_sym =>/=/andP[/negbTE->].
  Qed.

  Lemma basis_reachable (s:seq nat) (init:state s):
    cyclic_K -> reflect (reachable init) (state2vec init \in <<basis s>>%VS).
  Proof.
    rewrite -eq_statebasis -eq_surface_statebasis'. exact /reachableP.
  Qed.


  Lemma free_exn0 (n:nat) r (v:exp_vectType (regular_vectType K) n):
    free r -> v \in r -> exists c, v c != 0%R.
  Proof.
    rewrite free_directv =>/andP[H0r _ Hv].
    have : v <> 0%R => Hv0; [by move : Hv0 Hv H0r =>->->|].
    apply /existsP. rewrite -negb_forall; apply /negP =>/forallP => H0.
      by apply /Hv0/ffunP => i; rewrite !ffunE; apply /eqP.
  Qed.

  Lemma span_all0 (n:nat) (v:exp_vectType (regular_vectType K) n) r c:
    v \in <<r>>%VS ->
          all (fun x:exp_vectType (regular_vectType K) n
               => x c == 0%R) r -> v c = 0%R.
  Proof.
    elim : r =>[|x r IH] in v *;
                 [by rewrite span_nil memv0 =>/eqP->; rewrite ffunE|].
    rewrite span_cons =>/memv_addP[u0 /vlineP[k ->]][u Hu]/=->/andP[/eqP Hx].
      by rewrite !ffunE Hx scaler0 add0r =>/(IH _ Hu).
  Qed.

  Lemma free_basis_sub_lemma (n:nat) (s:seq nat):
    free (basis s) ->
      free [seq @state2vec (n.+1 :: s) x
           | x <- flatten
                    [seq map
                         (fun f:state s =>
                            [ffun x => if val x.1 == i then f x.2 else 0%R])
                         (statebasis s) | i <- iota 0 n]].
  Proof.
    move => Hbasis. move : (Hbasis) =>/myfreeP[Huniq Hbasis']. apply /myfreeP.
    split =>[|v0].
    - rewrite map_inj_in_uniq 1?(perm_uniq (permEl (perm_catC _ _)))
      =>[|x y _ _]; [|exact /(@state2vec_inj (_ :: s))].
      apply /allpairs_uniq =>[||x y]; rewrite ?iota_uniq //.
      + move : Huniq. rewrite map_inj_in_uniq =>// x y _ _.
        exact /state2vec_inj.
      + move =>/allpairsP[[x1 x2]/=[Hx1 Hx2->]]/allpairsP[[y1 y2]/=[Hy1 Hy2]].
        move : Hx1 Hy1. rewrite !mem_iota /= add0n =>/leq_trans.
        move =>/(_ _ (leqnSn _)) Hx1 /leq_trans/(_ (leqnSn _)) Hy1->/=.
        move =>/ffunP H. case : (free_exn0 Hbasis (map_f _ Hx2)) =>[c0 /eqP].
        move : (H (Ordinal Hx1,ord2hyperspace c0)). rewrite !ffunE /= eq_refl.
        case : ifP =>[/eqP H1 _|]// Hc0. congr(_, _)=>//. apply /ffunP => c.
        move : H1 (H (Ordinal Hx1,c)) =><-. by rewrite !ffunE /= eq_refl.
    - move =>/mapP[x0]/allpairsP[x []]. rewrite mem_iota /= add0n =>/ltn_trans.
      move =>/(_ _ (ltnSn _)) => Hx1 Hx2 ->->. apply /negP => H.
      move : (Hbasis' (state2vec x.2)). rewrite map_f =>// /(_ (erefl _))/negP.
      apply. have : all (fun i => i < n.+1) (iota 0 n);
               [by apply /allP => i;
                           rewrite mem_iota add0n =>/ltn_trans/(_ (ltnSn _))|].
      elim : (iota 0 n) (iota_uniq 0 n) H =>[|m rm IHrm]/=.
      + rewrite span_nil memv0 =>_/eqP/ffunP H _.
        suff ->: state2vec x.2 = 0%R by exact /mem0v. apply /ffunP => c.
        move : (H (@hyperspace2ord (n.+1 :: s)
                                   (Ordinal Hx1, ord2hyperspace c))).
          by rewrite !ffunE hyperspace2ordK /= eq_refl.
      + rewrite map_cat filter_cat span_cat =>/andP[Hm Hrm]/memv_addP[u Hu].
        case =>[v Hv] Huv /andP[Hmn Hall].
        have Hvm0 : forall c m' (Hm':m' < n.+1),
            m' = m ->
            v (@hyperspace2ord (_ :: s) (Ordinal Hm',c)) = 0%R
        =>[c m' Hm' Hmm|];
        [apply /(span_all0 Hv)/allP => y;
         rewrite mem_filter =>/andP[_/mapP[a0 /allpairsP[a [Ha1 Ha2 ->]]]->];
         rewrite !ffunE hyperspace2ordK /= Hmm;
           by case : ifP Ha1 Hm =>// /eqP->->|].
        case : (@eqP _ x.1 m) => Hx1m.
        * rewrite filter_map -(@eq_filter _ (fun x1 => x1 != x.2))
          =>[|a]/=; [|by congr(~~ _);
                      apply /(sameP eqP)/(iffP eqP)=>[/state2vec_inj|->]].
          have ->: state2vec x.2 =
          [ffun a => u (@hyperspace2ord (_ :: s)
                                        (Ordinal Hmn, ord2hyperspace a))];
            [by apply /ffunP => a;
             move : Huv =>/ffunP
                        /(_ (@hyperspace2ord
                               (_ :: s) (Ordinal Hmn, ord2hyperspace a)));
             rewrite !ffunE hyperspace2ordK (Hvm0 _ _ _ (erefl _)) addr0 /=
                     Hx1m eq_refl|].
          elim : (statebasis s) u Hu {Huv} =>[|b r IHr]/= u;
            [by rewrite !span_nil !memv0 =>/eqP->; apply /eqP/ffunP => z;
             rewrite !ffunE|].
          move => Hu. case : ifP =>[/negbTE|/negPn] Hb; case : ifP Hu.
          -- rewrite !span_cons =>_/memv_addP[u' /vlineP[k ->]][u1 Hu1]->.
             apply /memv_addP.
             exists (k *: state2vec b)%R; [by apply /vlineP; exists k|].
             exists [ffun a =>
                     u1 (@hyperspace2ord (_ :: s)
                                         (Ordinal Hmn, ord2hyperspace a))];
                  [exact : (IHr _ Hu1)|apply /ffunP => a; rewrite 3!ffunE].
             symmetry. rewrite 4!ffunE /= ord2hyperspaceK. rewrite !ffunE.
               by rewrite /ord2hyperspace mulordK /= eq_refl.
          -- rewrite Hx1m. move =>/negPn/eqP/ffunP H. have //: false.
             rewrite -Hb. apply /eqP/ffunP => a.
             move : (H (@hyperspace2ord (_ :: s) (Ordinal Hx1,a))).
               by rewrite !ffunE hyperspace2ordK /= Hx1m eq_refl.
          -- move : Hb Hx1m =>/eqP<-->. by rewrite eq_refl.
          -- by move =>_/IHr.
        * apply /IHrm =>//. move : add0r (Huv) Hv.
          suff -> : u = 0%R =>[-><-|]//. apply /ffunP => a. move : Huv.
          move =>/ffunP/(_ a). rewrite !ffunE.
          case : (@eqP nat_eqType (@ord2hyperspace (_ :: s) a).1 m) => Ham.
          -- case : ifP =>[/eqP<-|]// Ha1 in Hx1m *.
             rewrite -[a](@ord2hyperspaceK (_ :: s)). move : Ham.
             move : (@ord2hyperspace (_ :: _) a) =>/=[[m' Hm'] b]/= Hmm.
               by rewrite (Hvm0 _ _ _ Hmm) addr0 =><-.
          -- move =>_. apply /(span_all0 Hu)/allP => z. rewrite mem_filter.
             move =>/andP[_/mapP[z' /mapP[y _]->]->]. rewrite !ffunE.
               by case : ifP Ham =>[/eqP|].
  Qed.


  Lemma free_basis (s:seq nat): free (basis s).
  Proof.
    elim : s =>[|[|n] s IH]/=; try exact /nil_free. rewrite map_cat.
    apply /free_catP. split =>[|v0 /mapP[x0 /allpairsP[x [Hx1 Hx2->->]]]|].
    - rewrite -map_cat map_inj_in_uniq 1?(perm_uniq (permEl (perm_catC _ _)))
      =>[|x y _ _]; [rewrite cat_uniq|exact /(@state2vec_inj (_ :: s))].
      apply /and3P. split; [|apply /hasPn|].
      + apply /allpairs_uniq =>[||x y]; rewrite ?iota_uniq //.
        * move : (free_uniq IH). rewrite map_inj_in_uniq =>// x y _ _.
          exact /state2vec_inj.
        * move =>/allpairsP[[x1 x2]/=[Hx1 Hx2->]]/allpairsP[[y1 y2]/=[Hy1 Hy2]].
          move : Hx1 Hy1. rewrite !mem_iota /= add0n =>/leq_trans.
          move =>/(_ _ (leqnSn _)) Hx1 /leq_trans/(_ (leqnSn _)) Hy1->/=.
          move =>/ffunP H. case : (free_exn0 IH (map_f _ Hx2)) =>[c0 /eqP].
          move : (H (Ordinal Hx1,ord2hyperspace c0)). rewrite !ffunE /= eq_refl.
          case : ifP =>[/eqP H1 _|]// Hc0. congr(_, _)=>//. apply /ffunP => c.
          move : H1 (H (Ordinal Hx1,c)) =><-. by rewrite !ffunE /= eq_refl.
      + move => f0 /codomP[c ->]/=. apply /allpairsP =>[[x [Hx1 Hx2]]].
        move =>/ffunP =>/(_ (Ordinal (ltnSn _),c)). rewrite !ffunE eq_refl.
        case : ifP Hx1 =>[|_ _/eqP]; [|by rewrite oner_eq0].
        move =>/eqP<-/=. by rewrite mem_iota ltnn.
      + rewrite codomE map_inj_in_uniq ?enum_uniq =>// c d _ _/ffunP.
        move =>/(_ (ord0,c)). rewrite !ffunE /= eq_refl.
        case : ifP =>[/eqP|_/eqP]//. by rewrite oner_eq0.
    - apply /memv_addP =>[[v1 Hv1][u1 Hu1] Hv1u1].
      have Hx : @state2vec (_ :: s)
                             [ffun z =>
                              if val z.1 == x.1 then x.2 z.2 else 0%R] \in
          [seq @state2vec (n.+1 :: s) x
          | x <- flatten
                   [seq map
                        (fun f:state s =>
                           [ffun x => if val x.1 == i then f x.2 else 0%R])
                        (statebasis s) | i <- iota 0 n]]
        by apply /map_f/allpairsP; exists x; split.
      have Hu10': forall c:hyperspace s,
          u1 (@hyperspace2ord (_ :: s) (Ordinal (ltnSn _),c)) = 0%R;
            [|have Hv10 : v1 = 0%R; [|have Hu10 : u1 = 0%R]].
      + move => c. apply /(span_all0 Hu1)/allP => y0. rewrite mem_filter.
        move =>/andP[_/mapP[y1 /allpairsP[y []]]]. rewrite mem_iota add0n.
        move => Hy1 Hy2 ->->. rewrite !ffunE hyperspace2ordK /=.
          by case : ifP ltnn Hy1 =>// /eqP->->.
      + apply /ffunP. move : Hv1 Hv1u1. rewrite codomE.
        elim : (enum (hyperspace s)) v1 (enum_uniq (hyperspace s))
        =>[|y r IHr]/= v1; [by rewrite span_nil memv0 =>_/eqP->|move =>/andP[]].
        move => Hy Huniq. rewrite span_cons =>/memv_addP[v11 /vlineP[k ->]].
        case =>[u11 Hu11]-> H a.
        have H0 : u11 (@hyperspace2ord (_ :: s) (Ordinal (ltnSn n),y)) = 0%R.
        * elim : r u11 Hy Hu11 {H IHr Huniq}
          =>[|z r IHr]/= u11;
              [by rewrite span_nil memv0 =>_/eqP->; rewrite ffunE|].
          rewrite in_cons negb_or span_cons =>/andP[/negbTE Hz Huniq].
          move =>/memv_addP[b /vlineP[j ->]][u11' /(IHr _ Huniq) H]->.
          move : (hyperspace2ordK y). rewrite !ffunE /ord2hyperspace mulordK.
          move =>->/=. by rewrite Hz H scaler0 addr0.
        * move : H (H) =>/ffunP/(_ (@hyperspace2ord (_ :: s)
                                                  (Ordinal (ltnSn n),y))).
          rewrite !ffunE hyperspace2ordK H0 Hu10' /= eq_refl !addr0.
          move : Hx1. rewrite mem_iota add0n /=.
          case : ifP =>[/eqP<-|_ _/esym/eqP]; [by rewrite ltnn|].
          rewrite scaler_eq0 oner_eq0 orbF =>/eqP->. rewrite !scale0r !add0r.
          move =>/(IHr _ Huniq Hu11)->. by rewrite ffunE.
      + apply /ffunP. move : Hv10 add0r Hv1u1 Hu1 =>->-><-. move =>/negPn.
          by move : (free_basis_sub_lemma n IH) =>/myfreeP[_/(_ _ Hx)->].
      + move : Hv1u1 Hx (free_basis_sub_lemma n IH). rewrite free_directv Hv10.
          by rewrite Hu10 addr0 =>->->.
    - move => x0' /mapP[x0'' /codomP[c ->]->]. rewrite -span_cat. apply /negP.
      move =>/(@span_all0 _ _ _
                          (@hyperspace2ord (_ :: s) (Ordinal (ltnSn _),c))).
      rewrite !ffunE hyperspace2ordK eq_refl all_cat => H.
      suff : 1%R = (0%R : regular_vectType K) =>[/eqP|]; [by rewrite oner_eq0|].
      apply /H/andP. split; apply /allP => x; [rewrite mem_filter =>/andP[Hx]|];
      move =>/mapP[a0]; [move =>/codomP[a -> Hex]|move =>/allpairsP[y []]].
      + apply /eqP. move : Hex Hx =>->. rewrite !ffunE hyperspace2ordK /=.
        case : ifP =>// /eqP->. by rewrite eq_refl.
      + rewrite mem_iota add0n => Hy1 _->->. rewrite !ffunE hyperspace2ordK /=.
        apply /eqP. case : ifP Hy1 =>// /eqP->. by rewrite ltnn.
  Qed.


  Lemma card_hyperspace (s:seq nat): #|hyperspace s| = \prod_(n <- s) n.
  Proof.
    elim : s =>[|n s IH]/=; rewrite ?big_nil ?card_unit // big_cons.
      by rewrite card_prod card_ord IH.
  Qed.

  Lemma dim_basis (s:seq nat):
    \dim <<basis s>>%VS = \prod_(n <- s) n - \prod_(n <- s) n.-1.
  Proof.
    rewrite (dim_free (free_basis s)).
    elim : s =>[|n s IH]/=; [by rewrite !big_nil|rewrite !big_cons].
    case : n =>[|n]//=. move : IH. rewrite !size_map size_cat size_codom.
    rewrite card_hyperspace size_allpairs size_iota =>->. rewrite mulnBr.
    rewrite addnBA -?mulSn // leq_mul2l. apply /orP. right. (*apply /leq_prod.*)
    elim : s =>[|m s IH]/=; rewrite ?big_nil // !big_cons. apply /leq_mul =>//.
    exact /leq_pred.
  Qed.


  (**********)
  (* answer *)
  (**********)

  (* the problem can be solved when (K = F_2, s = [n; n; n]) *)

  Definition tppmark_1 (s:seq nat):
    cyclic_K -> forall init:state s,
      reflect (reachable init) (state2vec init \in <<basis s>>%VS) :=
    fun Hc init => basis_reachable init Hc.

  Definition tppmark_2 (s:seq nat): free (basis s) := free_basis _.

  Definition tppmark_3 (s:seq nat):
    \dim <<basis s>> = \prod_(n <- s) n - \prod_(n <- s) n.-1 := dim_basis _.
End Tppmark.
