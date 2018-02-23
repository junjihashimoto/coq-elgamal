From mathcomp Require Import all_ssreflect all_algebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import intZmod.
Import intOrdered.
Import GRing.Theory.
Open Scope ring_scope.

Section Reversible.
  Definition enc1 (m n:int) := m - n.
  Definition enc2 (m n:int) := ((m + n) %/ 2)%Z.

  Definition dec1 (e1: int) (e2: int) := ((e1 + e2 * 2 + 1) %/2)%Z.
  Definition dec2 (e1: int) (e2: int) := dec1 e1 e2 - e1.
 
  Lemma addmn (m n:int) : (m + (- n) + m + n) = m * (2:int).
  Proof.
    rewrite addrC.
    rewrite [m + (-n) + m]addrC.
    rewrite [m + (m + (-n))]addrA.
    rewrite [m + m + (-n)]addrC addrA.
    rewrite addrN add0r.
    rewrite -{1}[m]mulr1.
    rewrite -{2}[m]mulr1.
    rewrite -mulrDr //=.
  Qed.


  Lemma divmn (d:int) : d - (d %% 2)%Z = (d %/ 2)%Z * 2.
  Proof.
    apply/subr0_eq.
    rewrite -opprB.
    rewrite [-(d - (d %% 2)%Z)]opprB addrA.
    rewrite -divz_eq //=.
    rewrite opprB.
    rewrite addrN //.
  Qed.

  Lemma lezrl (n m:int): lez n m = (n <= m).
  Proof.
    rewrite /lez //=.
  Qed.

  Lemma ltzrl (n m:int): ltz n m = (n < m).
  Proof.
    rewrite /ltz //=.
  Qed.

  Lemma lt_d_1 (d:int) : (d %% 2)%Z <= 1 .
  Proof.
    have lt_2 : (d %% 2)%Z < `|Posz 2| .
    - rewrite ltz_mod //.
    have eq_2 : `|Posz 2| = Posz 2.
    - by [].
    have eq_21 : (d %% 2)%Z < 2 .
    - rewrite -{2}eq_2 lt_2 //
    rewrite ltz_mod //.
    rewrite -ltz_add1r //.
  Qed.

  Lemma modDiv0 (d:int) : ((1 - (d %% 2)%Z) %/ 2)%Z = 0%Z.
  Proof.
    rewrite divz_small //.
    (* 0 <= 1 - (d %% 2)%Z < `|2|%N *)
    rewrite -lezrl subz_ge0 lezrl lt_d_1 /=.
    rewrite -lez_add1r addrA.
    rewrite -lezrl -subz_ge0 lezrl.
    have eq_2 : 1 + 1 = (2:int).
    - by [].
    have eq0_2 : (2:int) + (-(2:int)) = 0.
    - by [].
    rewrite addrC opprB /=.
    rewrite eq_2.
    rewrite [(d %% 2)%Z + (-(2:int))]addrC addrC addrA eq0_2.
    rewrite add0r.
    rewrite modz_ge0 //.
  Qed.

  Theorem dec1_correct (m n :int): dec1 (enc1 m n) (enc2 m n) = m.
  Proof.
    rewrite /dec1 /enc1 /enc2.
    rewrite -divmn.
    rewrite !addrA.
    rewrite [m - n + m + n]addmn.
    have divrMDl2 (m0: int): ((m * (Posz 2) + m0) %/ (Posz 2))%Z = m + (m0 %/ (Posz 2))%Z.
    - rewrite divzMDl //.
    rewrite {1}addrC !addrA.
    rewrite [1 + m * 2]addrC.
    set mn := - ((m + n) %% 2)%Z.
    rewrite -/mn.
    set mn1 := 1 + mn.
    rewrite addrC addrA.
    rewrite addrC addrA.
    rewrite -/mn1.
    rewrite addrC.
    rewrite divrMDl2.
    rewrite /mn1 /mn modDiv0.
    rewrite addr0 //.
  Qed.

  Theorem dec2_correct (m n :int): dec2 (enc1 m n) (enc2 m n) = n.
  Proof.
    rewrite /dec2.
    rewrite dec1_correct /enc1.
    rewrite [-(m - n)]opprB addrA.
    rewrite addrC addrA addNr add0r //.
  Qed.
End Reversible.
