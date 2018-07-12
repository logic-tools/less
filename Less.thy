\<comment> \<open>Substitutionless First-Order Logic: A Formal Soundness Proof\<close>

theory Less imports Main begin

type_synonym proxy = \<open>unit list\<close>

type_synonym arity = proxy

type_synonym var = proxy

datatype form = Pre proxy arity | Eq var var | Neg form | Imp form form | Uni var form

primrec eval :: \<open>(var \<Rightarrow> 'a) \<Rightarrow> arity \<Rightarrow> 'a list\<close> where
  \<open>eval _ [] = []\<close> |
  \<open>eval e (_ # n) = e n # eval e n\<close>

primrec semantics :: \<open>(var \<Rightarrow> 'a) \<Rightarrow> (proxy \<Rightarrow> 'a list \<Rightarrow> bool) \<Rightarrow> form \<Rightarrow> bool\<close> where
  \<open>semantics e g (Pre i n) = g i (eval e n)\<close> |
  \<open>semantics e g (Eq x y) = (e x = e y)\<close> |
  \<open>semantics e g (Neg p) = (\<not> semantics e g p)\<close> |
  \<open>semantics e g (Imp p q) = (semantics e g p \<longrightarrow> semantics e g q)\<close> |
  \<open>semantics e g (Uni x p) = (\<forall>t. semantics (e(x := t)) g p)\<close>

primrec no_occur_in :: \<open>var \<Rightarrow> form \<Rightarrow> bool\<close> where
  \<open>no_occur_in z (Pre _ n) = (length z \<ge> length n)\<close> |
  \<open>no_occur_in z (Eq x y) = (z \<noteq> x \<and> z \<noteq> y)\<close> |
  \<open>no_occur_in z (Neg p) = no_occur_in z p\<close> |
  \<open>no_occur_in z (Imp p q) = (no_occur_in z p \<and> no_occur_in z q)\<close> |
  \<open>no_occur_in z (Uni _ p) = no_occur_in z p\<close>

abbreviation \<open>fail \<equiv> Uni [] (Eq [] [])\<close>

inductive OK :: \<open>form \<Rightarrow> bool\<close> ("\<turnstile> _" 0) where
  \<open>\<turnstile> pq \<Longrightarrow> \<turnstile> p \<Longrightarrow> \<turnstile> case pq of Imp p' q \<Rightarrow> if p' = p then q else fail | _ \<Rightarrow> fail\<close> |
  \<open>\<turnstile> p \<Longrightarrow> \<turnstile> Uni x p\<close> |
  \<open>\<turnstile> Imp (Imp p q) (Imp (Imp q r) (Imp p r))\<close> |
  \<open>\<turnstile> Imp (Imp (Neg p) p) p\<close> |
  \<open>\<turnstile> Imp p (Imp (Neg p) q)\<close> |
  \<open>\<turnstile> Imp (Uni x (Imp p q)) (Imp (Uni x p) (Uni x q))\<close> |
  \<open>\<turnstile> if no_occur_in x p then Imp p (Uni x p) else fail\<close> |
  \<open>\<turnstile> Imp (Neg (Uni x p)) (Uni x (Neg (Uni x p)))\<close> |
  \<open>\<turnstile> Imp (Uni x (Uni y p)) (Uni y (Uni x p))\<close> |
  \<open>\<turnstile> Neg (Uni x (Neg (Eq x y)))\<close> |
  \<open>\<turnstile> Imp (Eq x y) (Imp (Eq x z) (Eq y z))\<close> |
  \<open>\<turnstile> if x \<noteq> y then Imp (Eq x y) (Imp p (Uni x (Imp (Eq x y) p))) else fail\<close>

theorem soundness: \<open>\<turnstile> p \<Longrightarrow> semantics e g p\<close>
proof (induct p arbitrary: e rule: OK.induct)
  case (1 pq) show ?case by (cases pq) (use 1 in auto)
next
  case 7
  have *: \<open>length x \<ge> length n \<Longrightarrow> eval e n = eval (e(x := t)) n\<close> for x n e and t :: 'a
    by (induct n) auto
  have \<open>no_occur_in x p \<Longrightarrow> semantics e g p = semantics (e(x := t)) g p\<close> for x p e g and t :: 'a
  proof (induct p arbitrary: e)
    case Pre show ?case by (smt Pre * no_occur_in.simps semantics.simps)
  next
    case Uni show ?case by (smt Uni fun_upd_twist fun_upd_upd no_occur_in.simps semantics.simps)
  qed auto
  then show ?case by auto
next
  case 9 show ?case by (smt fun_upd_twist semantics.simps)
next
  case 12 show ?case by (smt fun_upd_same fun_upd_triv fun_upd_twist semantics.simps)
qed auto

end

\<comment> \<open>Andreas Halkjær From, John Bruntse Larsen, Anders Schlichtkrull & Jørgen Villadsen\<close>
