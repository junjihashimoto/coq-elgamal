From mathcomp Require Import ssreflect ssrbool ssrnat eqtype.
From mathcomp Require Import prime div cyclic.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Elgamal.
Variable p g : nat.
Variable prime_p : prime p.
Variable prime_g : prime g.

Variable pri : nat.
Hypothesis pri_lt_p : pri < p.
Hypothesis g_lt_p : g < p.

Variable r : nat.
Hypothesis r_lt_p : r < p.

Definition pub := (g ^ pri) %% p.

Definition enc1 := g ^ r %% p.
Definition enc2 (m : nat) := (pub ^ r * m) %% p.

Definition dec (e1 : nat) (e2 : nat) := e2 * ((e1 ^ (p - 2)) ^ pri) %% p.

Lemma ex1 : (g ^ pri %% p) ^ r = g ^ (pri * r) %[mod p].
Proof.
by rewrite modnXm expnM.
Qed.

Lemma ex2 : (g ^ r %% p) ^ ((p - 2) * pri) = g ^ (r *(p - 2) * pri) %[mod p].
Proof.
rewrite modnXm !expnM //.
Qed.

Lemma ex3: pri * r * (p - 2) + pri * r = pri * r * (p - 1).
Proof.
rewrite -{2}[pri * r]muln1.
rewrite -mulnDr.
have pluslemma : (p - 2) +1 = p - 1.
- rewrite addn1.
  apply subnSK.
  by rewrite prime_gt1.
rewrite pluslemma //.
Qed.

Lemma phi_prime : forall x, prime x -> totient x = x.-1.
Proof.
move=> x; move/totient_pfactor; move/(_ _ (ltn0Sn 0)).
by rewrite expn1 expn0 muln1.
Qed.

Lemma gp_coprime: coprime g p.
Proof.
rewrite prime_coprime //.
rewrite dvdn_prime2 //.
rewrite neq_ltn.
rewrite g_lt_p.
by [].
Qed.

Lemma ex5: g ^ (p - 1) %% p = 1.
Proof.
rewrite subn1.
rewrite -phi_prime.
rewrite Euler_exp_totient.
- rewrite modn_small //.
- rewrite prime_gt1 //.
- rewrite gp_coprime //.
- rewrite prime_p //.
Qed.

Theorem elgamal_correct1 :
 forall w : nat, w < p -> dec enc1 (enc2 w) = w %[mod p].
Proof.
move => w w_le_p.
rewrite /dec.
rewrite modn_mod.
rewrite /enc1 /enc2 /pub.
rewrite modnMml.
rewrite -expnM.
rewrite -modnMm.
rewrite -[((g ^ pri %% p) ^ r * w) %% p ]modnMm.
rewrite ex1.

rewrite [(g ^ (pri * r) %% p * (w %% p)) %% p]modnMm.
rewrite ex2.

rewrite modnMm.
rewrite mulnC.
rewrite mulnA.
rewrite -expnD.
rewrite -[_ * pri]mulnC. 
rewrite [pri * _]mulnA.
rewrite ex3.

rewrite -[pri * r * (p - 1)]mulnC expnM.
rewrite -modnMml.
rewrite -modnXm.
rewrite ex5.

rewrite exp1n.
rewrite modnMml.
rewrite mul1n.
by [].
Qed.

End Elgamal.
