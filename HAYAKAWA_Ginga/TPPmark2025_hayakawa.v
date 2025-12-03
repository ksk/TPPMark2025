From mathcomp Require Import ssrnat ssrbool fintype eqtype seq ssreflect.
Require Import Coq.Logic.FunctionalExtensionality.

(* n*n*nのキューブ　trueが点灯、falseが消灯で、各引数は座標を表す　*)
Definition cube(n:nat) := 'I_(S n) -> 'I_(S n) -> 'I_(S n) -> bool.

(* キューブ同士の和　xor回路で, 2キューブの同座標がon同士の場合offになる *)
Definition plus{n:nat}(A B:cube n):cube n :=
fun x y z => A x y z != B x y z.

(* 全て消灯の状態　これを目指す *)
Definition off{n:nat} : cube n := fun x y z => false.

(* キューブの和に対する基本性質　可換性や結合測 *)
Lemma plus_eq{n:nat}(A:cube n):plus A A = off.
Proof.
apply/functional_extensionality=>x.
apply/functional_extensionality=>y.
apply/functional_extensionality=>z.
rewrite/plus.
by case(A x y z).
Qed.
Theorem plus_c{n:nat}(A B:cube n):plus A B = plus B A.
Proof.
rewrite/plus.
apply/functional_extensionality=>x.
apply/functional_extensionality=>y.
apply/functional_extensionality=>z.
by case:(A x y z);case:(B x y z).
Qed.
Theorem plus_a{n:nat}(A B C:cube n):plus (plus A B) C = plus A (plus B C).
Proof.
rewrite/plus.
apply/functional_extensionality=>x.
apply/functional_extensionality=>y.
apply/functional_extensionality=>z.
by case:(A x y z);case:(B x y z);case:(C x y z).
Qed.
Lemma off_plus{n:nat}(A:cube n):plus A off = A.
rewrite/plus/off.
apply/functional_extensionality=>x.
apply/functional_extensionality=>y.
apply/functional_extensionality=>z.
by case:(A x y z).
Qed.
Lemma plus_off{n:nat}(A B:cube n): plus A B = off <-> A = B.
Proof.
split=>H.
by rewrite-(off_plus B)plus_c-(plus_eq A)plus_a H off_plus.
by rewrite H plus_eq.
Qed.


(* 許容されるボタン操作　正確にはこれらの裏からも操作可能だが、変わらないので無視 *)
Definition push_x{n:nat}(a b:'I_(S n)):cube n:=
fun x y z => (y == a) && (z == b).
Definition push_y{n:nat}(a b:'I_(S n)):cube n:=
fun x y z => (x == b) && (z == a).
Definition push_z{n:nat}(a b:'I_(S n)):cube n:=
fun x y z => (x == a) && (y == b).

(*
与えられたキューブＡに対し、リストに対応するボタン操作を有限回繰り返す関数
option boolは操作可能な3面にそれぞれ対応しており、扱いやすい3値の有限型として採用している
*)
Fixpoint switch{n:nat}(A:cube n)(s:seq (option bool* 'I_(S n)* 'I_(S n))) : cube n :=
match s with
|nil => A
|(Some true, a, b)::s' => plus (switch A s') (push_x a b)
|(Some false, a, b)::s' => plus (switch A s') (push_y a b)
|(None, a, b)::s' => plus (switch A s') (push_z a b)
end.

(*
リスト内に特定の要素が奇数回か判定する関数
スイッチは偶数回押すと戻るため、上記のswitch関数の結果を表す際に非常に有効
*)
Fixpoint is_odd{t:eqType}(x:t)(s:seq t):=
match s with
|nil => false
|h::s' => (h == x) != (is_odd x s')
end.

(*
各座標に対して、対応するスイッチ3種が合計奇数回押されたとき点灯している
偶数のときは消灯
*)
Lemma is_oddP{n:nat}(s:seq (option bool* 'I_(S n)* 'I_(S n)))(x y z:'I_(S n)):
(is_odd (Some true, y, z) s)!=(is_odd (Some false, z, x) s)!=(is_odd (None, x, y) s)=switch off s x y z.
Proof.
have H0:forall (a d:option bool)(b c e f:'I_(S n)), ((a, b, c) == (d, e, f)) = ((d==a)&&(e==b)&&(f==c)).
move=>a d b c e f.
have H0:forall a b,(a == b) = (b == a) by[].
by rewrite H0.
elim:s;[done|]=>[[[[[]|]]]a b] s H/=;rewrite H0/=/plus-{}H/push_x/push_y/push_z H0 H0/=.
by case(y==a);case(z==b);case(is_odd (Some true, y, z) s);case(is_odd (Some false, z, x) s);
case_eq(is_odd (None, x, y) s)=>H1;rewrite H1/=.
by case(x==b);case(z==a);case(is_odd (Some true, y, z) s);case(is_odd (Some false, z, x) s);
case_eq(is_odd (None, x, y) s)=>H1;rewrite H1/=.
by case(x==a);case(y==b);case(is_odd (Some true, y, z) s);case(is_odd (Some false, z, x) s);
case_eq(is_odd (None, x, y) s)=>H1;rewrite H1/=.
Qed.


(* 便宜上、0に対応する値に名づけしておく *)
Lemma le0 (n:nat):0 < S n. done. Qed.
Definition Zero {n:nat}:'I_(S n) := Ordinal (le0 n).


(* 操作する3面が全て消灯しているかチェックする関数 *)
Definition surface_off{n:nat}(A:cube n) : Prop :=
forall i j, (A Zero i j)=false /\ (A i Zero j)=false /\ (A i j Zero)=false.


(*
offの状態からスイッチを押して出来たキューブの三面が消灯しているとき、全て消灯している。

証明概略：
(証明済み補題：任意の点に対して対応するスイッチが3種あり、そのスイッチが押された回数の偶奇で消灯点灯が定まる。）

offから遷移してできたキューブを用意し、ある角を手前にもってくる。
任意のスイッチの内点を選んだとき、その点から手前3面に進んだ突き当りにある3点、
さらにそれら3点から手前3辺へ進んだ突き当りにある3点、手前角の合計8点について考える。
それらに対応するスイッチは合計12種類あり、各スイッチがそれぞれ2点の状態を変化させる。
すなわち、初期状態の点灯数0からどのスイッチを押しても8点のうち奇数個のランプが点灯することは無い。
ここで、選んだ8点のうち7点は表面にあるため、表面が全てoffならば内部の点もoffである。
すなわち、offの状態からスイッチ操作で遷移したキューブにおいて、
表面のランプが全てoffならば全てのランプがoffである。

なお、以下の形式証明中ではここまで論理だてておらず、2^12の総当たりで解いている。
ＱＥＤ．


これはスイッチ操作で表面を変化させることなく内部を変化させることは不可能であることを示しており、
これでほとんど解決なのだが、実は厳密には表面をoffに揃えるアルゴリズムが存在することを示す必要がある。
*)
Theorem surface_to_all{n:nat}(s:seq (option bool*'I_(S n)*'I_(S n))): surface_off (switch off s) -> (switch off s) = off.
Proof.
rewrite/surface_off=>H.
apply/functional_extensionality=>x.
apply/functional_extensionality=>y.
apply/functional_extensionality=>z.
rewrite/off.
move:(H x y)=>[_][_]H1.
move:(H y z)=>[H2 _].
move:(H x z)=>[_][H3 _].
move:(H Zero y)=>[_][_]H4.
move:(H Zero z)=>[H5 _].
move:(H x Zero)=>[_][H6 _].
move:(H Zero Zero)=>[{}H _].
repeat rewrite-is_oddP in H H1 H2 H3 H4 H5 H6 *.
repeat (destruct (is_odd _ _);try done).
Qed.










(* スイッチ操作に関する簡単な補題 *)
Lemma switch_plus{n:nat}(A:cube n)(s:seq (option bool*'I_(S n)*'I_(S n))):
  switch A s = plus A (switch off s).
Proof.
elim:s.
by rewrite/=off_plus.
by move=>[[[[]|]]i j] s H;rewrite/=H plus_a.
Qed.
Lemma switch_cat{n:nat}{A:cube n}:
  forall x y, switch A (x ++ y) = plus (switch off x) (switch A y).
Proof.
move=>x y.
elim:x;[by rewrite plus_c off_plus|]=>[[[[[]|]]]a b] x H;
by rewrite/=H plus_a (plus_c _ (_ a b)) plus_a.
Qed.

(* 1面をoffに揃える関数 *)
Fixpoint align_x_line{n:nat}(A:cube n)(i:'I_(S n))(s:seq 'I_(S n)):=
match s with
|nil => nil
|h::s' =>
  if A Zero i h then
    (Some true, i, h)::(align_x_line A i s')
  else
    (align_x_line A i s')
end.
Fixpoint align_x_surface{n:nat}(A:cube n)(s:seq 'I_(S n)):=
match s with
|nil => nil
|h::s' => (align_x_line A h (enum 'I_(S n)))++(align_x_surface A s')
end.

(* １面を揃えたとき、表面が点灯してた座標のランプは全て反転する *)
Lemma alignxP{n:nat}(A:cube n):
let Ax := switch A (align_x_surface A (enum 'I_(S n))) in
forall i j k, Ax k i j != A k i j = A Zero i j.
Proof.
move=>Ax i j k.
rewrite/Ax.
have:i\in enum 'I_(S n) by apply mem_enum.
have:uniq (enum 'I_(S n))by apply enum_uniq.
elim:(enum 'I_(S n));[done|]=>h e H.
rewrite inE/==>/andP[]hnin/H{}H.
case_eq(i==h)=>[/eqP|] H0.
rewrite-{h H}H0 in hnin *=>_.
rewrite/=switch_plus switch_cat/plus.
have{hnin}H:switch off (align_x_surface A e) k i j = false.
elim:e hnin;[done|]=>h e H.
rewrite inE negb_or=>/andP[]/eqP H0/H{}H/=.
rewrite switch_cat/plus{}H.
apply/eqP.
elim:(enum _);[done|]=>h'{}e H/=.
case:(A Zero h h');[|done].
by rewrite/=/plus{}H/push_x(_:i==h=false);[|apply/eqP].
rewrite{}H.
have H:switch off (align_x_line A i (enum 'I_n.+1)) k i j = A Zero i j.
have:j\in enum 'I_(S n) by apply mem_enum.
have:uniq (enum 'I_(S n))by apply enum_uniq.
elim:(enum _);[done|]=>h{}e H.
rewrite inE/==>/andP[]hnin/H{}H.
case_eq(j==h)=>[/eqP H0 _|H0].
rewrite-{H h}H0 in hnin *.

have{hnin}H0:switch off (align_x_line A i e) k i j=false.
move:hnin.
elim:e;[done|]=>h e H.
rewrite inE negb_or=>/andP[]/eqP H0/H{}H/=.
case:(A Zero i h);[|done].
rewrite/=/plus{}H/push_x(_:i==i);[|done].
rewrite(_:j==h=false);by [|apply/eqP].

case(A Zero i j);[|done].
rewrite/=/plus/push_x/=(_:i==i);[|done].
by rewrite H0(_:j==j)/=;[|done].
move/H=>{}H.
case:(A Zero i h);[|done].
rewrite/=/plus{}H/push_x H0(_:i == i);[|done].
by case:(A Zero i j).
rewrite H.
by case(A Zero i j);case(A k i j).

move/H=>{}H.
rewrite switch_cat/plus/=.
have H1:forall a b c, (a!=b!=c) = (a!=(b!=c)).
move=>a b c.
by destruct a, b, c.
rewrite{}H1{}H.
suff H:switch off (align_x_line A h (enum 'I_n.+1)) k i j = false.
rewrite H.
by case(A Zero i j).
elim:(enum _);[done|]=>h'{hnin}e H/=.
case:(A Zero h h');[|done].
by rewrite/=/plus{e}H/push_x H0.
Qed.

(* 操作する3平面それぞれが全てoffになっているか判定 *)
Definition x_off{n:nat}(A:cube n):=forall i j, A Zero i j = false.
Definition y_off{n:nat}(A:cube n):=forall i j, A i Zero j = false.
Definition z_off{n:nat}(A:cube n):=forall i j, A i j Zero = false.


(* 正面はいかなる状態からでもoffに揃える *)
Lemma alignPx{n:nat}{A:cube n}:
x_off (switch A (align_x_surface A (enum 'I_(S n)))).
Proof.
move=>i j.
move:(alignxP A i j Zero).
by case(A Zero i j);case(switch A (align_x_surface A (enum 'I_n.+1)) Zero i j).
Qed.

(* 側面が揃っているときは崩さない *)
Lemma alignPy{n:nat}(A:cube n):
y_off A -> y_off (switch A (align_x_surface A (enum 'I_(S n)))).
Proof.
rewrite/y_off=>H i j.
move:(alignxP A Zero j i).
rewrite H H.
by case(switch A (align_x_surface A (enum 'I_n.+1)) i Zero j).
Qed.
Lemma alignPz{n:nat}(A:cube n):
z_off A -> z_off (switch A (align_x_surface A (enum 'I_(S n)))).
Proof.
rewrite/z_off=>H i j.
move:(alignxP A j Zero i).
rewrite H H.
by case(switch A (align_x_surface A (enum 'I_n.+1)) i j Zero).
Qed.



(*
キューブの回転操作　具体的には、1つの角が正面を向くように持ったとき、
その角を中心に反時計回りに120度回転させる
*)
Definition spin{n:nat}(A:cube n):cube n:= fun x y z=> A y z x.

(* キューブの和はスピン操作と可換 *)
Lemma plus_spin{n:nat}(A B:cube n):plus (spin A) (spin B) = spin (plus A B).
Proof. done. Qed.

(* スイッチ操作コマンドもキューブの回転に併せて回す *)
Fixpoint spin'{n:nat}(s:seq (option bool*'I_(S n)*'I_(S n))):=
match s with
|(Some true, i, j)::s' => (Some false, i, j)::spin' s'
|(Some false, i, j)::s' => (None, i, j)::spin' s'
|(None, i, j)::s' => (Some true, i, j)::spin' s'
|nil => nil
end.

(* x軸、y軸に沿ったボタン操作は、スピンによりy軸、z軸に移る *)
Lemma spin_pushx{n:nat}:forall i j:'I_(S n), spin(push_x i j) = push_y i j.
Proof.
move=>i j.
rewrite/spin/push_x/push_y.
apply/functional_extensionality=>x.
apply/functional_extensionality=>_.
apply/functional_extensionality=>z.
by case:(z==i);case(x==j).
Qed.
Lemma spin_pushy{n:nat}:forall i j:'I_(S n), spin(push_y i j) = push_z i j.
Proof.
move=>i j.
by rewrite-spin_pushx/push_x/push_z/spin.
Qed.


(* スイッチを押す操作もスピンと可換 *)
Lemma switch_spin{n:nat}(A:cube n):forall s, switch (spin A) (spin' s) = spin(switch A s).
Proof.
elim;[done|]=>[[[[[]|]]]a b] s H;rewrite/=H-plus_spin;f_equal.
by rewrite spin_pushx.
by rewrite spin_pushy.
Qed.
Lemma spin'P{n:nat}(A:cube n):forall s, switch (spin A) (spin' s) = spin(switch A s).
Proof.
elim;[done|]=>[[[[[]|]]]a b] s H;rewrite/=H-plus_spin;f_equal.
by rewrite spin_pushx.
by rewrite spin_pushy.
Qed.



(*
表面をoffに揃えるアルゴリズム
具体的には、一面を揃えて回転させる操作を3回繰り返す
*)
Definition align{n:nat}(A:cube n):=
let sx := align_x_surface A (enum 'I_(S n)) in
let Ax := switch A sx in
let sy := align_x_surface (spin Ax) (enum 'I_(S n)) in
let Ay := switch (spin Ax) sy in
let sz := align_x_surface (spin Ay) (enum 'I_(S n)) in
sx ++ spin'(spin'(sy)) ++ spin'(sz).


(* 軽い補題群 *)
Lemma spin_off{n:nat}:@spin n off = off.
Proof. done. Qed.
Lemma spin_loop{n:nat}(A:cube n):spin(spin(spin A)) = A.
Proof. done. Qed.



(* 表面を揃えるアルゴリズムが機能している事を保証 *)
Lemma alignP{n:nat}(A:cube n):surface_off(switch A (align A)).
Proof.
rewrite/align switch_plus switch_cat-plus_a-switch_plus-switch_plus.
remember(switch A (align_x_surface A (enum 'I_n.+1)))as Ax.
rewrite switch_cat.
remember(switch (spin Ax) (align_x_surface (spin Ax) (enum 'I_n.+1)))as Ay.
rewrite-spin_off-spin_off spin'P spin'P switch_plus-{1}(plus_eq (spin Ax)).
rewrite plus_a-switch_plus-HeqAy.
rewrite-{2}(spin_loop Ax) spin'P plus_spin switch_plus-(plus_spin _ Ay) plus_a.
rewrite-(plus_a (spin Ay))(plus_c(spin Ay))plus_a-switch_plus.
remember(switch (spin Ay) (align_x_surface (spin Ay) (enum 'I_n.+1)))as Az.
rewrite-plus_spin spin_loop-plus_spin spin_loop-plus_a plus_eq.
suff H:surface_off Az=>[i j|].
rewrite/plus/off/spin.
move:(H i j)=>[_][_ H0].
move:(H j i)=>[H1][H2] _.
by rewrite H0 H1 H2.
suff:x_off Az/\y_off Az/\z_off Az=>[[]H[]H0 H1 i j|].
by rewrite H H0 H1.
rewrite HeqAz.
split.
apply/alignPx.
split.
apply/alignPy.
suff H:x_off Ay=>[i j|].
by rewrite/spin H.
rewrite HeqAy.
apply/alignPx.
apply/alignPz.
suff H:y_off Ay=>[i j|].
by rewrite/spin H.
rewrite HeqAy.
apply/alignPy.
suff H:x_off Ax=>[i j|].
by rewrite/spin H.
rewrite HeqAx.
apply/alignPx.
Qed.



(*
ようやく本題
特定のアルゴリズムに沿って三面をoffに揃えたとき全てのランプがoffになっていることが、
offにできるための必要十分条件

align:任意のキューブが与えられたとき、表三面を揃える操作手順リストを返すアルゴリズム
switch:指定のキューブに対し、操作手順リストに沿ってボタン操作を繰り返す関数
*)
Theorem TPPmark2025{n:nat}(A:cube n):switch A (align A) = off <-> exists s, switch A s = off.
Proof.
split=>H.
by exists (align A).
case:H=>s H.
move:(alignP A).
rewrite switch_plus switch_plus-{1}H switch_plus plus_a-switch_cat-plus_a plus_eq plus_c
off_plus=>/surface_to_all H0.
rewrite switch_cat plus_off in H0.
by rewrite-switch_plus-H0-switch_plus H.
Qed.