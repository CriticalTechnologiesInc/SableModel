(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory Corres_UL
imports
  "nicta_lib/Crunch"
  "nicta_lib/Monad_WP/wp/WPEx"
  "nicta_lib/HaskellLemmaBucket"
begin

text {* Definition of correspondence *}

definition
  corres_underlying :: "(('s \<times> 't) set) \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow>
                        ('a \<Rightarrow> ('b \<times> 't) \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> ('t \<Rightarrow> bool)
           \<Rightarrow> ('s, 'a) nondet_monad \<Rightarrow> ('t, 'b) nondet_monad \<Rightarrow> bool"
where
 "corres_underlying srel nf nf' rrel G G' \<equiv> \<lambda>m m'.
      \<forall>(s, s') \<in> srel. G s \<and> G' s' \<longrightarrow>
           (nf \<longrightarrow> \<not> snd (m s)) \<longrightarrow>
           (\<forall>(r', t') \<in> fst (m' s'). \<exists>(r, t) \<in> fst (m s). (t, t') \<in> srel \<and> rrel r (r', t')) \<and> 
           (nf' \<longrightarrow> \<not> snd (m' s'))"

(* Return value rv' does not depend on the associated state *)
definition 
  r_state_inv :: "('a \<Rightarrow> ('b \<times> 's) \<Rightarrow> bool) \<Rightarrow> bool"
where
  "r_state_inv r \<equiv> (\<forall>rv rv' s s'. r rv (rv', s) = r rv (rv', s'))"

text {* Base case facts about correspondence *}

lemma corres_underlyingD:
  "\<lbrakk> corres_underlying R nf nf' rs P P' f f'; (s,s') \<in> R; P s; P' s'; nf \<longrightarrow> \<not> snd (f s) \<rbrakk>
  \<Longrightarrow> (\<forall>(r',t')\<in>fst (f' s'). \<exists>(r,t)\<in>fst (f s). (t, t') \<in> R \<and> rs r (r', t')) \<and> (nf' \<longrightarrow> \<not> snd (f' s'))"
  by (fastforce simp: corres_underlying_def)

lemma corres_underlyingD2:
  "\<lbrakk> corres_underlying R nf nf' rs P P' f f'; (s,s') \<in> R; P s; P' s'; (r',t')\<in>fst (f' s'); nf \<longrightarrow> \<not> snd (f s) \<rbrakk>
  \<Longrightarrow> \<exists>(r,t)\<in>fst (f s). (t, t') \<in> R \<and> rs r (r', t')"
  by (fastforce dest: corres_underlyingD)

lemma propagate_no_fail:
  "\<lbrakk> corres_underlying S nf True R P P' f f';
        no_fail P f; \<forall>s'. P' s' \<longrightarrow> (\<exists>s. P s \<and> (s,s') \<in> S) \<rbrakk> 
  \<Longrightarrow> no_fail P' f'"
  apply (clarsimp simp: corres_underlying_def no_fail_def)
  apply (erule allE, erule (1) impE)
  apply clarsimp
  apply (drule (1) bspec, clarsimp)
  done

lemma corres_underlying_serial:
  "\<lbrakk> corres_underlying S False True rrel G G' m m'; empty_fail m' \<rbrakk> \<Longrightarrow>
     \<forall>s. (\<exists>s'. (s,s') \<in> S \<and> G s \<and> G' s') \<longrightarrow> fst (m s) \<noteq> {}"
  apply (clarsimp simp: corres_underlying_def empty_fail_def)
  apply (drule_tac x="(s, s')" in bspec, simp)
  apply (drule_tac x=s' in spec)
  apply auto
  done

(* FIXME: duplicated with HOL.iff_allI *)
lemma All_eqI:
  assumes ass: "\<And>x. A x = B x"
  shows "(\<forall>x. A x) = (\<forall>x. B x)"
  apply (subst ass)
  apply (rule refl)
  done

lemma corres_singleton:
 "corres_underlying sr nf nf' r P P' (\<lambda>s. ({(R s, S s)},x)) (\<lambda>s. ({(R' s, S' s)},False))
  = (\<forall>s s'. P s \<and> P' s' \<and> (s, s') \<in> sr \<and> (nf \<longrightarrow> \<not> x)
          \<longrightarrow> ((S s, S' s') \<in> sr \<and> r (R s) ((R' s'), S' s')))"
  by (auto simp: corres_underlying_def)

lemma corres_return[simp]:
  "corres_underlying sr nf nf' r P P' (return a) (return b) =
   (\<forall>s s'. P s \<and> P' s' \<and> (s, s') \<in> sr \<longrightarrow> r a (b, s'))"
  by (simp add: return_def corres_singleton)

lemma corres_get[simp]:
 "corres_underlying sr nf nf' r P P' get get =
  (\<forall>s s'. (s, s') \<in> sr \<and> P s \<and> P' s' \<longrightarrow> r s (s', s'))"
  apply (simp add: get_def corres_singleton)
  apply (rule All_eqI)+
  apply safe
  done

lemma corres_gets[simp]:
 "corres_underlying sr nf nf' r P P' (gets a) (gets b) =
  (\<forall> s s'. P s \<and> P' s' \<and> (s, s') \<in> sr \<longrightarrow> r (a s) ((b s'), s'))"
  by (simp add: simpler_gets_def corres_singleton)

lemma corres_throwError[simp]:
  "corres_underlying sr nf nf' r P P' (throwError a) (throwError b) =
   (\<forall>s s'. P s \<and> P' s' \<and> (s, s') \<in> sr \<longrightarrow> r (Inl a) ((Inl b), s'))"
  by (simp add: throwError_def)

lemma corres_no_failI_base:
  assumes f: "nf \<Longrightarrow> no_fail P f"
  assumes f': "nf' \<Longrightarrow> no_fail P' f'"
  assumes corres: "\<forall>(s, s') \<in> S. P s \<and> P' s' \<longrightarrow>
                     (\<forall>(r', t') \<in> fst (f' s'). \<exists>(r, t) \<in> fst (f s). (t, t') \<in> S \<and> R r (r', t'))"
  shows "corres_underlying S nf nf' R P P' f f'"
  using assms by (simp add: corres_underlying_def no_fail_def)

(* This lemma gets the shorter name because many existing proofs want nf=False *)
lemma corres_no_failI:
  assumes f': "nf' \<Longrightarrow> no_fail P' f'"
  assumes corres: "\<forall>(s, s') \<in> S. P s \<and> P' s' \<longrightarrow>
                     (\<forall>(r', t') \<in> fst (f' s'). \<exists>(r, t) \<in> fst (f s). (t, t') \<in> S \<and> R r (r', t'))"
  shows "corres_underlying S False nf' R P P' f f'"
  using assms by (simp add: corres_underlying_def no_fail_def)

text {* A congruence rule for the correspondence functions. *}

lemma corres_cong:
  assumes P: "\<And>s. P s = P' s"
  assumes Q: "\<And>s. Q s = Q' s"
  assumes f: "\<And>s. P' s \<Longrightarrow> f s = f' s"
  assumes g: "\<And>s. Q' s \<Longrightarrow> g s = g' s"
  assumes r: "\<And>x y s t s' t'. \<lbrakk> P' s; Q' t; (x, s') \<in> fst (f' s); (y, t') \<in> fst (g' t) \<rbrakk>
                                \<Longrightarrow> r x (y, t') = r' x (y, t')"
  shows      "corres_underlying sr nf nf' r P Q f g = corres_underlying sr nf nf' r' P' Q' f' g'"
  apply (simp add: corres_underlying_def)
  apply (rule ball_cong [OF refl])
  apply (clarsimp simp: P Q)
  apply (rule imp_cong [OF refl])
  apply (clarsimp simp: f g)
  apply (rule imp_cong [OF refl])
  apply (rule conj_cong)
   apply (rule ball_cong [OF refl])
   apply clarsimp
   apply (rule bex_cong [OF refl])
   apply (clarsimp simp: r)
  apply simp
  done

text {* The guard weakening rule *}

lemma stronger_corres_guard_imp:
  assumes x: "corres_underlying sr nf nf' r Q Q' f g"
  assumes y: "\<And>s s'. \<lbrakk> P s; P' s'; (s, s') \<in> sr \<rbrakk> \<Longrightarrow> Q s"
  assumes z: "\<And>s s'. \<lbrakk> P s; P' s'; (s, s') \<in> sr \<rbrakk> \<Longrightarrow> Q' s'"
  shows      "corres_underlying sr nf nf' r P P' f g"
  using x by (auto simp: y z corres_underlying_def)

lemma corres_guard_imp:
  assumes x: "corres_underlying sr nf nf' r Q Q' f g"
  assumes y: "\<And>s. P s \<Longrightarrow> Q s" "\<And>s. P' s \<Longrightarrow> Q' s"
  shows      "corres_underlying sr nf nf' r P P' f g"
  apply (rule stronger_corres_guard_imp)
    apply (rule x)
   apply (simp add: y)+
  done

lemma corres_rel_imp:
  assumes x: "corres_underlying sr nf nf' r' P P' f g"
  assumes y: "\<And>x y. r' x y \<Longrightarrow> r x y"
  shows      "corres_underlying sr nf nf' r P P' f g"
  apply (insert x)
  apply (simp add: corres_underlying_def)
  apply clarsimp
  apply (drule (1) bspec, clarsimp)
  apply (drule (1) bspec, clarsimp)
  apply (blast intro: y)
  done

text {* Splitting rules for correspondence of composite monads *}

lemma corres_underlying_split:
  assumes ac: "corres_underlying s nf nf' r' G G' a c"
  assumes valid: "\<lbrace>G\<rbrace> a \<lbrace>P\<rbrace>" "\<lbrace>G'\<rbrace> c \<lbrace>P'\<rbrace>"
  assumes bd: "\<And>rv rv'. corres_underlying s nf nf' r (P rv)
                (\<lambda>s'. r' rv (rv', s') \<and> P' rv' s') (b rv) (d rv')"
  shows "corres_underlying s nf nf' r G G' (a >>= b) (c >>= d)"
using assms
unfolding corres_underlying_def bind_def valid_def Bex_def Ball_def
apply (clarsimp simp add: case_prod_beta)
apply (metis eq_snd_iff fst_conv)
done

text {* Derivative splitting rules *}

lemma corres_split':
  assumes x: "corres_underlying sr nf nf' r' P P' a c"
  assumes y: "\<And>rv rv'. corres_underlying sr nf nf' r (Q rv) (\<lambda>s'. r' rv (rv', s') \<and> Q' rv' s') (b rv) (d rv')"
  assumes    "\<lbrace>P\<rbrace> a \<lbrace>Q\<rbrace>" "\<lbrace>P'\<rbrace> c \<lbrace>Q'\<rbrace>"
  shows      "corres_underlying sr nf nf' r P P' (a >>= (\<lambda>rv. b rv)) (c >>= (\<lambda>rv'. d rv'))"
  by (fastforce intro!: corres_underlying_split assms)

lemma corres_split:
  assumes bd: "\<And>rv rv'. corres_underlying sr nf nf' r (R rv)
              (\<lambda>s'. r' rv (rv', s') \<and> R' rv' s') (b rv) (d rv')"
  assumes ac: "corres_underlying sr nf nf' r' P P' a c"
  assumes valid: "\<lbrace>Q\<rbrace> a \<lbrace>R\<rbrace>" "\<lbrace>Q'\<rbrace> c \<lbrace>R'\<rbrace>"
  shows "corres_underlying sr nf nf' r (P and Q) (P' and Q') (a >>= b) (c >>= d)"
proof (rule corres_underlying_split)
  show "corres_underlying sr nf nf' r' (P and Q) (P' and Q') a c"
    using ac unfolding corres_underlying_def by auto
next
  show "\<lbrace>P and Q\<rbrace> a \<lbrace>R\<rbrace>" using valid(1) unfolding valid_def by auto
next
  show "\<lbrace>P' and Q'\<rbrace> c \<lbrace>R'\<rbrace>" using valid(2) unfolding valid_def by auto
next
  fix rv rv'
  show "corres_underlying sr nf nf' r (R rv) (\<lambda>s'. r' rv (rv', s') \<and> R' rv' s') (b rv) (d rv')"
    using bd .
qed

(* LHS is a relation on errors, RHS a relation on values *)
primrec
  rel_sum_comb :: "('a \<Rightarrow> ('b \<times> 's) \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> ('d \<times> 's) \<Rightarrow> bool)
                     \<Rightarrow> ('a + 'c \<Rightarrow> ('b + 'd) \<times> 's \<Rightarrow> bool)" (infixl "\<oplus>" 95)
where
  "(f \<oplus> g) (Inr x) y = (let v = fst y in
                        let s = snd y in
                        \<exists>v'. v = Inr v' \<and> (g x (v', s)))"
| "(f \<oplus> g) (Inl x) y = (let e = fst y in
                        let s = snd y in
                        \<exists>e'. e = Inl e' \<and> (f x (e', s)))"

lemma rel_sum_comb_r2[simp]:
  "(f \<oplus> g) x ((Inr y), s) = (\<exists>x'. x = Inr x' \<and> g x' (y, s))"
  apply (case_tac x, simp_all)
  done

lemma rel_sum_comb_l2[simp]:
  "(f \<oplus> g) x ((Inl y), s) = (\<exists>x'. x = Inl x' \<and> f x' (y, s))"
  apply (case_tac x, simp_all)
  done

lemma corres_splitEE:
  fixes r'
  assumes bd: "\<And>rv rv'. corres_underlying sr nf nf' (f \<oplus> r) (R rv)
                (\<lambda>s'. r' rv (rv', s') \<and> R' rv' s') (b rv) (d rv')"
      and ac: "corres_underlying sr nf nf' (f \<oplus> r') P P' a c"
      and valid: "\<lbrace>Q\<rbrace> a \<lbrace>R\<rbrace>,\<lbrace>\<top>\<top>\<rbrace>" "\<lbrace>Q'\<rbrace> c \<lbrace>R'\<rbrace>,\<lbrace>\<top>\<top>\<rbrace>"
  shows      "corres_underlying sr nf nf' (f \<oplus> r) (P and Q) (P' and Q') (a >>=E b) (c >>=E d)"
unfolding bindE_def
proof (rule corres_split)
  fix rv rv' s'
  let ?R = "\<lambda>rv. case rv of Inl e \<Rightarrow> \<top> | Inr v \<Rightarrow> R v"
  let ?R' = "\<lambda>rv'. case rv' of Inl e \<Rightarrow> \<top> | Inr v \<Rightarrow> R' v"
  show "corres_underlying sr nf nf' (f \<oplus> r) (?R rv) (\<lambda>s'. (f \<oplus> r') rv (rv', s') \<and> ?R' rv' s')
    (lift b rv) (lift d rv')"
  proof (cases rv)
    fix e
    assume "rv = Inl e"
    thus ?thesis using bd unfolding corres_underlying_def Ball_def Bex_def
      by (clarsimp simp add: throwError_def return_def)
  next
    fix v
    assume "rv = Inr v"
    thus ?thesis using bd unfolding corres_underlying_def Ball_def Bex_def by clarsimp
  qed
next
  show "corres_underlying sr nf nf' (f \<oplus> r') P P' a c" using ac .
next
  show "\<lbrace>Q\<rbrace> a \<lbrace>\<lambda>a. case a of Inl e \<Rightarrow> \<lambda>_. True | Inr v \<Rightarrow> R v\<rbrace>"
    using valid(1) unfolding valid_def validE_def by (simp add: case_prod_unfold sum.case_eq_if)
next
  show "\<lbrace>Q'\<rbrace> c \<lbrace>\<lambda>a. case a of Inl e \<Rightarrow> \<lambda>_. True | Inr v \<Rightarrow> R' v\<rbrace>"
    using valid(2) unfolding valid_def validE_def by (simp add: case_prod_unfold sum.case_eq_if)
qed

lemma corres_split_handle:
  assumes bd: "\<And>e e'. corres_underlying sr nf nf' (f \<oplus> r) (E e)
              (\<lambda>s'. f' e (e', s') \<and> E' e' s') (b e) (d e')"
  assumes ac: "corres_underlying sr nf nf' (f' \<oplus> r) P P' a c"
  assumes valid: "\<lbrace>Q\<rbrace> a \<lbrace>\<top>\<top>\<rbrace>,\<lbrace>E\<rbrace>" "\<lbrace>Q'\<rbrace> c \<lbrace>\<top>\<top>\<rbrace>,\<lbrace>E'\<rbrace>"
  shows      "corres_underlying sr nf nf' (f \<oplus> r) (P and Q) (P' and Q') (a <handle> b) (c <handle> d)"
unfolding handleE_def handleE'_def
apply (rule corres_split)
  defer
  apply (rule ac)
  using valid(1) unfolding validE_def apply assumption
  using valid(2) unfolding validE_def apply assumption
  unfolding corres_underlying_def
  proof clarify
    fix rv rv' and s s'
    let ?b' = "case rv of Inl e \<Rightarrow> b e | Inr v' \<Rightarrow> return (Inr v')"
    let ?d' = "case rv' of Inl e \<Rightarrow> d e | Inr v' \<Rightarrow> return (Inr v')"
    assume sr: "(s, s') \<in> sr"
       and EE: "case rv of Inl e \<Rightarrow> E e s | Inr r \<Rightarrow> True"
       and f'r: "(f' \<oplus> r) rv (rv', s')"
       and EE': "case rv' of Inl e \<Rightarrow> E' e s' | Inr r \<Rightarrow> True"
       and nf_b': "nf \<longrightarrow> \<not>snd (?b' s)"
    show "(\<forall>(rr', t') \<in> fst (?d' s'). \<exists>(rr, t) \<in> fst (?b' s). (t, t') \<in> sr \<and> (f \<oplus> r) rr (rr', t')) \<and>
       (nf' \<longrightarrow> \<not> snd (?d' s'))"
    proof (cases rv)
      fix e
      assume e: "rv = Inl e"
      then obtain e' where e': "rv' = Inl e'" using ac and f'r
        unfolding corres_underlying_def by auto
      have "(\<forall>(rr', t') \<in> fst (d e' s').
        \<exists>(rr, t) \<in> fst (b e s). (t, t') \<in> sr \<and> (f \<oplus> r) rr (rr', t'))
        \<and> (nf' \<longrightarrow> \<not> snd (d e' s'))"
      proof -
        have f': "f' e (e', s')" using f'r e e' by auto
        have nf_b: "nf \<longrightarrow> \<not>snd (b e s)" using nf_b' e by auto
        from bd have "corres_underlying sr nf nf' (f \<oplus> r) (E e)
              (\<lambda>s'. f' e (e', s') \<and> E' e' s') (b e) (d e')" using e e' by simp
        with sr e e' EE EE' f' nf_b show "(\<forall>(r', t')\<in>fst (d e' s').
            \<exists>(ra, t)\<in>fst (b e s). (t, t') \<in> sr \<and> (f \<oplus> r) ra (r', t'))
            \<and> (nf' \<longrightarrow> \<not> snd (d e' s'))" unfolding corres_underlying_def by auto
      qed
      thus ?thesis using e e' by simp
    next
      fix v
      assume v: "rv = Inr v"
      then obtain v' where v': "rv' = Inr v'" using ac and f'r
        unfolding corres_underlying_def by auto
      have r: "r v (v', s')" using f'r v v' by auto
      with v v' and bd sr show ?thesis unfolding corres_underlying_def return_def by simp
    qed
  qed

lemma corres_split_catch:
  assumes bd: "\<And>e e'. corres_underlying sr nf nf' r (E e) (\<lambda>s'. f e (e', s') \<and> E' e' s') (b e) (d e')"
  assumes ac: "corres_underlying sr nf nf' (f \<oplus> r) P P' a c"
  assumes valid: "\<lbrace>Q\<rbrace> a \<lbrace>\<top>\<top>\<rbrace>,\<lbrace>E\<rbrace>" "\<lbrace>Q'\<rbrace> c \<lbrace>\<top>\<top>\<rbrace>,\<lbrace>E'\<rbrace>"
  shows      "corres_underlying sr nf nf' r (P and Q) (P' and Q') (a <catch> b) (c <catch> d)"
unfolding catch_def
apply (rule corres_split)
  defer
  apply (rule ac)
  using valid(1) unfolding validE_def apply assumption
  using valid(2) unfolding validE_def apply assumption
  unfolding corres_underlying_def
  proof clarify
    fix rv rv' and s s'
    let ?b' = "case rv of Inl e \<Rightarrow> b e | Inr v \<Rightarrow> return v"
    let ?d' = "case rv' of Inl e' \<Rightarrow> d e' | Inr v' \<Rightarrow> return v'"
    assume sr: "(s, s') \<in> sr"
       and EE: "case rv of Inl e \<Rightarrow> E e s | Inr r \<Rightarrow> True"
       and f'r: "(f \<oplus> r) rv (rv', s')"
       and EE': "case rv' of Inl e \<Rightarrow> E' e s' | Inr r \<Rightarrow> True"
       and nf_b': "nf \<longrightarrow> \<not>snd (?b' s)"
    show "(\<forall>(rr', t') \<in> fst (?d' s'). \<exists>(rr, t) \<in> fst (?b' s). (t, t') \<in> sr \<and> r rr (rr', t')) \<and>
       (nf' \<longrightarrow> \<not> snd (?d' s'))"
    proof (cases rv)
      fix e
      assume e: "rv = Inl e"
      then obtain e' where e': "rv' = Inl e'" using ac and f'r
        unfolding corres_underlying_def by auto
      have "(\<forall>(rr', t') \<in> fst (d e' s').
        \<exists>(rr, t) \<in> fst (b e s). (t, t') \<in> sr \<and> r rr (rr', t'))
        \<and> (nf' \<longrightarrow> \<not> snd (d e' s'))"
      proof -
        have f': "f e (e', s')" using f'r e e' by auto
        have nf_b: "nf \<longrightarrow> \<not>snd (b e s)" using nf_b' e by auto
        from bd have "corres_underlying sr nf nf' r (E e)
              (\<lambda>s'. f e (e', s') \<and> E' e' s') (b e) (d e')" using e e' by simp
        with sr e e' EE EE' f' nf_b show "(\<forall>(r', t')\<in>fst (d e' s').
            \<exists>(ra, t)\<in>fst (b e s). (t, t') \<in> sr \<and> r ra (r', t'))
            \<and> (nf' \<longrightarrow> \<not> snd (d e' s'))" unfolding corres_underlying_def by auto
      qed
      thus ?thesis using e e' by simp
    next
      fix v
      assume v: "rv = Inr v"
      then obtain v' where v': "rv' = Inr v'" using ac and f'r
        unfolding corres_underlying_def by auto
      have r: "r v (v', s')" using f'r v v' by auto
      with v v' and bd sr show ?thesis unfolding corres_underlying_def return_def by simp
    qed
  qed

definition
 "dc \<equiv> \<lambda>rv rv'. True"

lemma dc_simp[simp]: "dc a b"
  by (simp add: dc_def)

lemma dc_o_simp1[simp]: "dc \<circ> f = dc"
  by (simp add: dc_def o_def)

lemma dc_o_simp2[simp]: "dc x \<circ> f = dc x"
  by (simp add: dc_def o_def)

lemma corres_split_nor:
 "\<lbrakk> corres_underlying sr nf nf' r R R' b d; corres_underlying sr nf nf' dc P P' a c;
    \<lbrace>Q\<rbrace> a \<lbrace>\<lambda>x. R\<rbrace>; \<lbrace>Q'\<rbrace> c \<lbrace>\<lambda>x. R'\<rbrace> \<rbrakk>
 \<Longrightarrow> corres_underlying sr nf nf' r (P and Q) (P' and Q') (a >>= (\<lambda>rv. b)) (c >>= (\<lambda>rv. d))"
  by (rule corres_split, auto)

lemma corres_split_norE:
   "\<lbrakk> corres_underlying sr nf nf' (f \<oplus> r) R R' b d; corres_underlying sr nf nf' (f \<oplus> dc) P P' a c;
    \<lbrace>Q\<rbrace> a \<lbrace>\<lambda>x. R\<rbrace>, \<lbrace>\<top>\<top>\<rbrace>; \<lbrace>Q'\<rbrace> c \<lbrace>\<lambda>x. R'\<rbrace>,\<lbrace>\<top>\<top>\<rbrace> \<rbrakk>
 \<Longrightarrow> corres_underlying sr nf nf' (f \<oplus> r) (P and Q) (P' and Q') (a >>=E (\<lambda>rv. b)) (c >>=E (\<lambda>rv. d))"
  by (rule corres_splitEE, auto)

text {* Some rules for walking correspondence into basic constructs *}

lemma corres_if:
  "\<lbrakk> G = G'; corres_underlying sr nf nf' r P P' a c; corres_underlying sr nf nf' r Q Q' b d \<rbrakk>
    \<Longrightarrow> corres_underlying sr nf nf' r
                (if G then P else Q) (if G' then P' else Q')
                (if G then a else b) (if G' then c else d)"
  by simp

lemma corres_whenE:
  "\<lbrakk> G = G'; corres_underlying sr nf nf' (fr \<oplus> r) P P' f g; \<And>s'. r () ((), s') \<rbrakk>
     \<Longrightarrow> corres_underlying sr nf nf' (fr \<oplus> r) (\<lambda>s. G \<longrightarrow> P s) (\<lambda>s. G' \<longrightarrow> P' s) (whenE G f) (whenE G' g)"
  by (simp add: whenE_def returnOk_def)

lemmas corres_if2 = corres_if[unfolded if_apply_def2]
lemmas corres_when =
    corres_if2[where b="return ()" and d="return ()"
                and Q="\<top>" and Q'="\<top>" and r=dc, simplified,
                folded when_def]

lemma corres_if_r:
  "\<lbrakk> corres_underlying sr nf nf' r P P' a c; corres_underlying sr nf nf' r P Q' a d \<rbrakk>
   \<Longrightarrow> corres_underlying sr nf nf' r (P) (if G' then P' else Q')
                                     (a) (if G' then c  else d)"
  by (simp)

text {* Some equivalences about liftM and other useful simps *}

lemma snd_liftM [simp]:
  "snd (liftM t f s) = snd (f s)"
  by (auto simp: liftM_def bind_def return_def)

lemma corres_liftM_simp[simp]:
  "(corres_underlying sr nf nf' r P P' (liftM t f) g)
    = (corres_underlying sr nf nf' (r \<circ> t) P P' f g)"
  apply (simp add: corres_underlying_def
           handy_liftM_lemma Ball_def Bex_def)
  apply (rule All_eqI)+
  apply blast
  done

lemma corres_liftM2_simp[simp]:
 "corres_underlying sr nf nf' r P P' f (liftM t g) =
  corres_underlying sr nf nf' (\<lambda>x (x', s'). r x (t x', s')) P P' f g"
  apply (simp add: corres_underlying_def
           handy_liftM_lemma Ball_def)
  apply (rule All_eqI)+
  apply blast
  done

lemma corres_liftE_rel_sum[simp]:
 "corres_underlying sr nf nf' (f \<oplus> r) P P' (liftE m) (liftE m') = corres_underlying sr nf nf' r P P' m m'"
  by (simp add: liftE_liftM o_def)

text {* Support for proving correspondence to noop with hoare triples *}

lemma corres_noop:
  assumes P: "\<And>s. P s \<Longrightarrow> \<lbrace>\<lambda>s'. (s, s') \<in> sr \<and> P' s'\<rbrace> f \<lbrace>\<lambda>rv s'. (s, s') \<in> sr \<and> r x (rv, s')\<rbrace>"
  assumes nf': "\<And>s. \<lbrakk> P s; nf' \<rbrakk> \<Longrightarrow> no_fail (\<lambda>s'. (s, s') \<in> sr \<and> P' s') f"
  shows "corres_underlying sr nf nf' r P P' (return x) f"  
  apply (simp add: corres_underlying_def return_def)
  apply clarsimp
  apply (frule P)
  apply (insert nf')
  apply (clarsimp simp: valid_def no_fail_def)
  done

lemma corres_noopE:
  assumes P: "\<And>s. P s \<Longrightarrow> \<lbrace>\<lambda>s'. (s, s') \<in> sr \<and> P' s'\<rbrace> f \<lbrace>\<lambda>rv s'. (s, s') \<in> sr \<and> r x (rv, s')\<rbrace>,\<lbrace>\<lambda>r s. False\<rbrace>"
  assumes nf': "\<And>s. \<lbrakk> P s; nf' \<rbrakk> \<Longrightarrow> no_fail (\<lambda>s'. (s, s') \<in> sr \<and> P' s') f"
  shows "corres_underlying sr nf nf' (fr \<oplus> r) P P' (returnOk x) f"
proof -
  have Q: "\<And>P f Q E. \<lbrace>P\<rbrace>f\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>r s. case_sum (\<lambda>e. E e s) (\<lambda>r. Q r s) r\<rbrace>"
   by (simp add: validE_def)
  thus ?thesis
  apply (simp add: returnOk_def)
  apply (rule corres_noop)
   apply (rule hoare_post_imp)
    defer
    apply (rule Q)
    apply (rule P)
    apply assumption
   apply (erule(1) nf')
  apply (case_tac ra, simp_all)
  done
qed

(* this could be stronger in the no_fail part *)
lemma corres_noop2:
  assumes x: "\<And>s. P s  \<Longrightarrow> \<lbrace>op = s\<rbrace> f \<exists>\<lbrace>\<lambda>r. op = s\<rbrace>"
  assumes y: "\<And>s. P' s \<Longrightarrow> \<lbrace>op = s\<rbrace> g \<lbrace>\<lambda>r. op = s\<rbrace>"
  assumes z: "nf' \<Longrightarrow> no_fail P f" "nf' \<Longrightarrow> no_fail P' g"
  shows      "corres_underlying sr nf nf' dc P P' f g"
  apply (clarsimp simp: corres_underlying_def)
  apply (rule conjI)
   apply clarsimp
   apply (rule use_exs_valid)
    apply (rule exs_hoare_post_imp)
     prefer 2
     apply (rule x)
     apply assumption
    apply simp_all
   apply (subgoal_tac "ba = b")
    apply simp
   apply (rule sym)
   apply (rule use_valid[OF _ y], assumption+)
   apply simp
  apply (insert z)
  apply (clarsimp simp: no_fail_def)
  done

text {* Support for dividing correspondence along
        logical boundaries *}

lemma corres_disj_division:
  "\<lbrakk> P \<or> Q; P \<Longrightarrow> corres_underlying sr nf nf' r R S x y; Q \<Longrightarrow> corres_underlying sr nf nf' r T U x y \<rbrakk>
     \<Longrightarrow> corres_underlying sr nf nf' r (\<lambda>s. (P \<longrightarrow> R s) \<and> (Q \<longrightarrow> T s)) (\<lambda>s. (P \<longrightarrow> S s) \<and> (Q \<longrightarrow> U s)) x y"
  apply safe
   apply (rule corres_guard_imp)
     apply simp
    apply simp
   apply simp
  apply (rule corres_guard_imp)
    apply simp
   apply simp
  apply simp
  done

lemma corres_weaker_disj_division:
  "\<lbrakk> P \<or> Q; P \<Longrightarrow> corres_underlying sr nf nf' r R S x y; Q \<Longrightarrow> corres_underlying sr nf nf' r T U x y \<rbrakk>
     \<Longrightarrow> corres_underlying sr nf nf' r (R and T) (S and U) x y"
  apply (rule corres_guard_imp)
    apply (rule corres_disj_division)
      apply simp+
  done

lemma corres_symmetric_bool_cases:
  "\<lbrakk> P = P'; \<lbrakk> P; P' \<rbrakk> \<Longrightarrow> corres_underlying srel nf nf' r Q Q' f g;
        \<lbrakk> \<not> P; \<not> P' \<rbrakk> \<Longrightarrow> corres_underlying srel nf nf' r R R' f g \<rbrakk>
      \<Longrightarrow> corres_underlying srel nf nf' r (\<lambda>s. (P \<longrightarrow> Q s) \<and> (\<not> P \<longrightarrow> R s))
                                          (\<lambda>s. (P' \<longrightarrow> Q' s) \<and> (\<not> P' \<longrightarrow> R' s))
                                          f g"
  by (cases P, simp_all)

text {* Support for symbolically executing into the guards
        and manipulating them *}

lemma bind_noop[simp]: "do return (); f od = f" by auto

lemma corres_symb_exec_l:
  assumes xy: "\<And>rv. corres_underlying sr nf nf' r (Q rv) P' (x rv) y"
  assumes sr: "\<forall>s\<^sub>C. \<lbrace>\<lambda>s\<^sub>A. P s\<^sub>A \<and> (s\<^sub>A, s\<^sub>C) \<in> sr\<rbrace> m \<exists>\<lbrace>\<lambda>r s\<^sub>A. (s\<^sub>A, s\<^sub>C) \<in> sr\<rbrace>"
  assumes valid: "\<lbrace>P\<rbrace> m \<lbrace>Q\<rbrace>"
  assumes nf: "nf' \<Longrightarrow> no_fail P m"
  shows      "corres_underlying sr nf nf' r P P' (m >>= x) y"
apply (subst bind_noop[symmetric]) back back
apply (rule corres_guard_imp [where Q="P and P" and Q'="\<top> and P'"])
apply (rule corres_split [where r'="\<top>\<top>" and R="Q" and R'="\<lambda>r. P'"])
apply simp_all
apply (rule xy)
defer
apply (rule valid)
unfolding corres_underlying_def
proof (clarsimp, rule conjI)
  fix s\<^sub>C s\<^sub>A
  assume "(s\<^sub>A, s\<^sub>C) \<in> sr" and "P s\<^sub>A" and "nf \<longrightarrow> \<not> snd (m s\<^sub>A)"
  show "\<forall>(r\<^sub>C, s\<^sub>C') \<in> fst (return () s\<^sub>C). \<exists>(r\<^sub>A, s\<^sub>A') \<in> fst (m s\<^sub>A). (s\<^sub>A', s\<^sub>C') \<in> sr"
  proof clarify
    fix s\<^sub>C'
    assume "((), s\<^sub>C') \<in> fst (return () s\<^sub>C)"
    hence "s\<^sub>C' = s\<^sub>C" by (simp add: return_def)
    with sr and `(s\<^sub>A, s\<^sub>C) \<in> sr` and `P s\<^sub>A` show "\<exists>(r\<^sub>A, s\<^sub>A')\<in>fst (m s\<^sub>A). (s\<^sub>A', s\<^sub>C') \<in> sr"
      unfolding exs_valid_def by simp
  qed
next
  fix s\<^sub>C s\<^sub>A
  assume "(s\<^sub>A, s\<^sub>C) \<in> sr" and "P s\<^sub>A" and "nf \<longrightarrow> \<not> snd (m s\<^sub>A)"
  show "nf' \<longrightarrow> \<not> snd (return () s\<^sub>C)" unfolding return_def by simp
qed

lemma corres_symb_exec_r:
  assumes xy: "\<And>rv. corres_underlying sr nf nf' r P (Q' rv) x (y rv)"
  assumes valid: "\<lbrace>P'\<rbrace> m \<lbrace>Q'\<rbrace>"
  assumes sr: "\<forall>s\<^sub>A. \<lbrace>\<lambda>s\<^sub>C. P' s\<^sub>C \<and> (s\<^sub>A, s\<^sub>C) \<in> sr\<rbrace> m \<lbrace>\<lambda>r s\<^sub>C. (s\<^sub>A, s\<^sub>C) \<in> sr\<rbrace>"
  assumes nf: "nf' \<Longrightarrow> no_fail P' m"
  shows      "corres_underlying sr nf nf' r P P' x (m >>= y)"
apply (subst bind_noop[symmetric])
apply (rule corres_guard_imp [where Q="\<top> and P" and Q'="P' and P'"])
apply (rule corres_split [where r'="\<top>\<top>" and R="\<lambda>r. P" and R'="Q'"])
apply simp_all
apply (rule xy)
defer
apply (rule valid)
unfolding corres_underlying_def
proof (clarsimp, rule conjI)
  fix s\<^sub>A s\<^sub>C
  assume "(s\<^sub>A, s\<^sub>C) \<in> sr" and "P' s\<^sub>C"
  show "\<forall>(r\<^sub>C, s\<^sub>C') \<in> fst (m s\<^sub>C). \<exists>(r\<^sub>A, s\<^sub>A') \<in> fst (return ()  s\<^sub>A). (s\<^sub>A', s\<^sub>C') \<in> sr"
  proof clarify
    fix r\<^sub>C s\<^sub>C'
    assume "(r\<^sub>C, s\<^sub>C') \<in> fst (m s\<^sub>C)"
    with sr and `(s\<^sub>A, s\<^sub>C) \<in> sr` and `P' s\<^sub>C` show "\<exists>(r\<^sub>A, s\<^sub>A')\<in>fst (return () s\<^sub>A). (s\<^sub>A', s\<^sub>C') \<in> sr"
      unfolding valid_def return_def by fastforce
  qed
next
  fix s\<^sub>C s\<^sub>A
  assume "P' s\<^sub>C"
  thus "nf' \<longrightarrow> \<not> snd (m s\<^sub>C)" using nf unfolding no_fail_def by simp
qed

lemma corres_symb_exec_r_conj:
  assumes xy: "\<And>rv. corres_underlying sr nf nf' r Q (R' rv) x (y rv)"
  assumes valid: "\<lbrace>Q'\<rbrace> m \<lbrace>R'\<rbrace>"
  assumes sr: "\<And>s. \<lbrace>\<lambda>s'. (s, s') \<in> sr \<and> P' s'\<rbrace> m \<lbrace>\<lambda>rv s'. (s, s') \<in> sr\<rbrace>"
  assumes nf: "\<And>s. nf' \<Longrightarrow> no_fail (\<lambda>s'. (s, s') \<in> sr \<and> P' s') m"
  shows      "corres_underlying sr nf nf' r Q (P' and Q') x (m >>= y)"
apply (subst bind_noop[symmetric])
apply (rule corres_guard_imp [where Q="\<top> and Q" and Q'="P' and Q'"])
apply (rule corres_split [where r'="\<top>\<top>" and R="\<lambda>r. Q" and R'="R'"])
apply simp_all
apply (rule xy)
defer
apply (rule valid)
unfolding corres_underlying_def
proof (clarsimp, rule conjI)
  fix s\<^sub>A s\<^sub>C
  assume "(s\<^sub>A, s\<^sub>C) \<in> sr" and "P' s\<^sub>C"
  show "\<forall>(r\<^sub>C, s\<^sub>C') \<in> fst (m s\<^sub>C). \<exists>(r\<^sub>A, s\<^sub>A') \<in> fst (return ()  s\<^sub>A). (s\<^sub>A', s\<^sub>C') \<in> sr"
  proof clarify
    fix r\<^sub>C s\<^sub>C'
    assume "(r\<^sub>C, s\<^sub>C') \<in> fst (m s\<^sub>C)"
    with sr and `(s\<^sub>A, s\<^sub>C) \<in> sr` and `P' s\<^sub>C` show "\<exists>(r\<^sub>A, s\<^sub>A')\<in>fst (return () s\<^sub>A). (s\<^sub>A', s\<^sub>C') \<in> sr"
      unfolding valid_def return_def by fastforce
  qed
next
  fix s\<^sub>A s\<^sub>C
  assume "(s\<^sub>A, s\<^sub>C) \<in> sr" and "P' s\<^sub>C"
  thus "nf' \<longrightarrow> \<not> snd (m s\<^sub>C)" using nf unfolding no_fail_def by simp
qed

lemma corres_bind_return_r:
  "corres_underlying S nf nf' (\<lambda>x (y, s). r x ((h y), s)) P Q f g \<Longrightarrow> 
   corres_underlying S nf nf' r P Q f (do x \<leftarrow> g; return (h x) od)"
  by (fastforce simp: corres_underlying_def bind_def return_def)

lemma corres_underlying_symb_exec_l:
  "\<lbrakk> corres_underlying sr nf nf' dc P P' f (return ()); \<And>rv. corres_underlying sr nf nf' r (Q rv) P' (g rv) h;
     \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<rbrakk>
    \<Longrightarrow> corres_underlying sr nf nf' r P P' (f >>= g) h"
  apply (drule(1) corres_underlying_split)
    apply (rule return_wp)
   apply clarsimp
   apply (erule meta_allE, assumption)
  apply simp
  done

text {* Inserting assumptions to be proved later *}

lemma corres_req:
  assumes x: "\<And>s s'. \<lbrakk> (s, s') \<in> sr; P s; P' s' \<rbrakk> \<Longrightarrow> F"
  assumes y: "F \<Longrightarrow> corres_underlying sr nf nf' r P P' f g"
  shows      "corres_underlying sr nf nf' r P P' f g"
  apply (cases "F")
   apply (rule y)
   apply assumption
  apply (simp add: corres_underlying_def)
  apply clarsimp
  apply (subgoal_tac "F")
   apply simp
  apply (rule x, assumption+)
  done

(* Insert assumption to be proved later, on the left-hand (abstract) side *)
lemma corres_gen_asm:
  assumes x: "F \<Longrightarrow> corres_underlying sr nf nf' r P P' f g"
  shows "corres_underlying sr nf nf' r (P and (\<lambda>s. F)) P' f g"
  apply (rule corres_req[where F=F])
   apply simp
  apply (rule corres_guard_imp [OF x])
    apply simp+
  done

(* Insert assumption to be proved later, on the right-hand (concrete) side *)
lemma corres_gen_asm2:
  assumes x: "F \<Longrightarrow> corres_underlying sr nf nf' r P P' f g"
  shows "corres_underlying sr nf nf' r P (P' and (\<lambda>s. F)) f g"
  apply (rule corres_req[where F=F])
   apply simp
  apply (rule corres_guard_imp [OF x])
    apply simp+
  done

lemma corres_trivial:
 "corres_underlying sr nf nf' r \<top> \<top> f g \<Longrightarrow> corres_underlying sr nf nf' r \<top> \<top> f g"
  by assumption

lemma corres_assume_pre:
  assumes R: "\<And>s s'. \<lbrakk> P s; Q s'; (s,s') \<in> sr \<rbrakk> \<Longrightarrow> corres_underlying sr nf nf' r P Q f g"
  shows "corres_underlying sr nf nf' r P Q f g"
  apply (clarsimp simp add: corres_underlying_def)
  apply (frule (2) R)
  apply (clarsimp simp add: corres_underlying_def)
  apply blast
  done

lemma corres_guard_imp2:
  "\<lbrakk>corres_underlying sr nf nf' r Q P' f g; \<And>s. P s \<Longrightarrow> Q s\<rbrakk> \<Longrightarrow> corres_underlying sr nf nf' r P P' f g"
  by (blast intro: corres_guard_imp)
(* FIXME: names\<dots> (cf. corres_guard2_imp below) *)
lemmas corres_guard1_imp = corres_guard_imp2

lemma corres_guard2_imp:
  "\<lbrakk>corres_underlying sr nf nf' r P Q' f g; \<And>s. P' s \<Longrightarrow> Q' s\<rbrakk>
   \<Longrightarrow> corres_underlying sr nf nf' r P P' f g"
  by (drule (1) corres_guard_imp[where P'=P' and Q=P], assumption+)

lemma corres_initial_splitE:
"\<lbrakk> corres_underlying sr nf nf' (f \<oplus> r') P P' a c; 
   \<And>rv rv'. corres_underlying sr nf nf' (f \<oplus> r) (Q rv)
    (\<lambda>s'. r' rv (rv', s') \<and> Q' rv' s') (b rv) (d rv'); 
   \<lbrace>P\<rbrace> a \<lbrace>Q\<rbrace>, \<lbrace>\<lambda>r s. True\<rbrace>;
   \<lbrace>P'\<rbrace> c \<lbrace>Q'\<rbrace>, \<lbrace>\<lambda>r s. True\<rbrace>\<rbrakk>
\<Longrightarrow> corres_underlying sr nf nf' (f \<oplus> r) P P' (a >>=E b) (c >>=E d)"
  apply (rule corres_guard_imp [where Q="P and P" and Q'="P' and P'"])
    apply (rule corres_splitEE [where R="Q" and R'="Q'" and r'="r'"])
    apply simp_all
  done

lemma corres_assert_assume:
  "\<lbrakk> P' \<Longrightarrow> corres_underlying sr nf nf' r P Q f (g ()); \<And>s. Q s \<Longrightarrow> P' \<rbrakk> \<Longrightarrow> 
  corres_underlying sr nf nf' r P Q f (assert P' >>= g)"
  by (auto simp: bind_def assert_def fail_def return_def 
                 corres_underlying_def)

lemma corres_state_assert:
  "corres_underlying sr nf nf' rr P Q f (g ()) \<Longrightarrow>
   (\<And>s. Q s \<Longrightarrow> R s) \<Longrightarrow>
   corres_underlying sr nf nf' rr P Q f (state_assert R >>= g)"
  by (clarsimp simp: corres_underlying_def state_assert_def get_def assert_def
                     return_def bind_def)

lemma corres_stateAssert_assume:
  "\<lbrakk> corres_underlying sr nf nf' r P Q f (g ()); \<And>s. Q s \<Longrightarrow> P' s \<rbrakk> \<Longrightarrow>
   corres_underlying sr nf nf' r P Q f (stateAssert P' [] >>= g)"
  apply (clarsimp simp: bind_assoc stateAssert_def)
  apply (rule corres_symb_exec_r [OF _ get_sp])
    apply (rule corres_assert_assume)
     apply (rule corres_assume_pre)
     apply (erule corres_guard_imp, clarsimp+)
   apply (wp | rule no_fail_pre)+
   apply simp
   unfolding no_fail_def get_def apply auto
   done

lemma corres_stateAssert_implied:
  "\<lbrakk> corres_underlying sr nf nf' r P Q f (g ());
     \<And>s s'. \<lbrakk> (s, s') \<in> sr; P s; P' s; Q s' \<rbrakk> \<Longrightarrow> Q' s' \<rbrakk>
   \<Longrightarrow> corres_underlying sr nf nf' r (P and P') Q f (stateAssert Q' [] >>= g)"
  apply (clarsimp simp: bind_assoc stateAssert_def)
  apply (rule corres_symb_exec_r [OF _ get_sp])
    apply (rule corres_assume_pre)
    apply (rule corres_assert_assume)
     apply (erule corres_guard_imp, clarsimp+)
   apply (wp | rule no_fail_pre)+
   apply simp
   unfolding no_fail_def get_def apply auto
  done

lemma corres_assert:
  "corres_underlying sr nf nf' dc (%_. P) (%_. Q) (assert P) (assert Q)"
  by (clarsimp simp add: corres_underlying_def return_def)

lemma corres_split2:
  assumes corr: "\<And>a a' b b'. corres_underlying sr nf nf' r1 (P1 a b)
                  (\<lambda>s'. r a a' b b' s' \<and> P1' a' b' s') (H a b) (H' a' b')"
  and    corr': "corres_underlying sr nf nf' (\<lambda>(a, b).\<lambda>((a', b'), s'). r a a' b b' s') P P' 
                        (do a \<leftarrow> F; b \<leftarrow> G; return (a, b) od) 
                        (do a' \<leftarrow> F'; b' \<leftarrow> G'; return (a', b') od)"
  and       h1: "\<lbrace>P\<rbrace> do fx \<leftarrow> F; gx \<leftarrow> G; return (fx, gx) od \<lbrace>\<lambda>rv. P1 (fst rv) (snd rv)\<rbrace>"
  and       h2: "\<lbrace>P'\<rbrace> do fx \<leftarrow> F'; gx \<leftarrow> G'; return (fx, gx) od \<lbrace>\<lambda>rv. P1' (fst rv) (snd rv)\<rbrace>"  
  shows "corres_underlying sr nf nf' r1 P P' 
                (do a \<leftarrow> F; b \<leftarrow> G; H a b od) 
                (do a' \<leftarrow> F'; b' \<leftarrow> G'; H' a' b' od)"
proof -
  have "corres_underlying sr nf nf' r1 P P' 
               ((do a \<leftarrow> F; b \<leftarrow> G; return (a, b) od) >>= (\<lambda>(a, b). H a b)) 
               ((do a' \<leftarrow> F'; b' \<leftarrow> G'; return (a', b') od) >>= (\<lambda>(a', b'). H' a' b'))"
    apply (rule corres_split')
    using assms apply auto
    done
  hence "corres_underlying sr nf nf' r1 P P' 
               (do a \<leftarrow> F; b \<leftarrow> G; rv \<leftarrow> return (a, b); H (fst rv) (snd rv) od) 
               (do a' \<leftarrow> F'; b' \<leftarrow> G'; rv' \<leftarrow> return (a', b'); H' (fst rv') (snd rv') od)"
    by (simp add: bind_assoc)
  thus ?thesis by simp
qed


lemma corres_split3:
  assumes corr: "\<And>a a' b b' c c'. corres_underlying sr nf nf' r1 (P1 a b c)
                     (\<lambda>s'. r a a' b b' c c' s' \<and> P1' a' b' c' s') (H a b c) (H' a' b' c')"
  and    corr': "corres_underlying sr nf nf' (\<lambda>(a, b, c).\<lambda>((a', b', c'), s'). r a a' b b' c c' s') P P' 
                        (do a \<leftarrow> A; b \<leftarrow> B a; c \<leftarrow> C a b; return (a, b, c) od) 
                        (do a' \<leftarrow> A'; b' \<leftarrow> B' a'; c' \<leftarrow> C' a' b'; return (a', b', c') od)"
  and       h1: "\<lbrace>P\<rbrace> 
                    do a \<leftarrow> A; b \<leftarrow> B a; c \<leftarrow> C a b; return (a, b, c) od 
                 \<lbrace>\<lambda>(a, b, c). P1 a b c\<rbrace>"
  and       h2: "\<lbrace>P'\<rbrace> 
                    do a' \<leftarrow> A'; b' \<leftarrow> B' a'; c' \<leftarrow> C' a' b'; return (a', b', c') od 
                 \<lbrace>\<lambda>(a', b', c'). P1' a' b' c'\<rbrace>"
  shows "corres_underlying sr nf nf' r1 P P' 
                (do a \<leftarrow> A; b \<leftarrow> B a; c \<leftarrow> C a b; H a b c od) 
                (do a' \<leftarrow> A'; b' \<leftarrow> B' a'; c' \<leftarrow> C' a' b'; H' a' b' c' od)"
proof -
  have "corres_underlying sr nf nf' r1 P P' 
               ((do a \<leftarrow> A; b \<leftarrow> B a; c \<leftarrow> C a b; return (a, b, c) od) >>= (\<lambda>(a, b, c). H a b c)) 
               ((do a' \<leftarrow> A'; b' \<leftarrow> B' a'; c' \<leftarrow> C' a' b'; return (a', b', c') od) >>= (\<lambda>(a', b', c'). H' a' b' c'))"
    apply (rule corres_split')
    using assms apply auto
    done
  hence "corres_underlying sr nf nf' r1 P P' 
               (do a \<leftarrow> A; b \<leftarrow> B a; c \<leftarrow> C a b; rv \<leftarrow> return (a, b, c); 
                          H (fst rv) (fst (snd rv)) (snd (snd rv)) od) 
               (do a' \<leftarrow> A'; b' \<leftarrow> B' a'; c' \<leftarrow> C' a' b'; rv \<leftarrow> return (a', b', c'); 
                          H' (fst rv) (fst (snd rv)) (snd (snd rv)) od)"
    by (simp add: bind_assoc)
  thus ?thesis by simp
qed

(* A little broken --- see above *)
lemma corres_split4:
  assumes corr: "\<And>a a' b b' c c' d d'. corres_underlying sr nf nf' r1 (P1 a b c d)
                  (\<lambda>s'. r a a' b b' c c' d d' s' \<and> P1' a' b' c' d' s') 
                                  (H a b c d) (H' a' b' c' d')"
  and    corr': "corres_underlying sr nf nf' (\<lambda>(a, b, c, d).\<lambda>((a', b', c', d'), s'). r a a' b b' c c' d d' s') P P' 
                        (do a \<leftarrow> A; b \<leftarrow> B; c \<leftarrow> C; d \<leftarrow> D; return (a, b, c, d) od) 
                        (do a' \<leftarrow> A'; b' \<leftarrow> B'; c' \<leftarrow> C'; d' \<leftarrow> D'; return (a', b', c', d') od)"
  and       h1: "\<lbrace>P\<rbrace> 
                    do a \<leftarrow> A; b \<leftarrow> B; c \<leftarrow> C; d \<leftarrow> D; return (a, b, c, d) od 
                 \<lbrace>\<lambda>(a, b, c, d). P1 a b c d\<rbrace>"
  and       h2: "\<lbrace>P'\<rbrace> 
                    do a' \<leftarrow> A'; b' \<leftarrow> B'; c' \<leftarrow> C'; d' \<leftarrow> D'; return (a', b', c', d') od 
                 \<lbrace>\<lambda>(a', b', c', d'). P1' a' b' c' d'\<rbrace>"
  shows "corres_underlying sr nf nf' r1 P P' 
                (do a \<leftarrow> A; b \<leftarrow> B; c \<leftarrow> C; d \<leftarrow> D; H a b c d od) 
                (do a' \<leftarrow> A'; b' \<leftarrow> B'; c' \<leftarrow> C'; d' \<leftarrow> D'; H' a' b' c' d' od)"
proof -  
  have "corres_underlying sr nf nf' r1 P P' 
               ((do a \<leftarrow> A; b \<leftarrow> B; c \<leftarrow> C; d \<leftarrow> D; return (a, b, c, d) od)
                >>= (\<lambda>(a, b, c, d). H a b c d)) 
               ((do a' \<leftarrow> A'; b' \<leftarrow> B'; c' \<leftarrow> C'; d' \<leftarrow> D'; return (a', b', c', d') od)
                >>= (\<lambda>(a', b', c', d'). H' a' b' c' d'))"
    apply (rule corres_split')
    using assms apply auto
    done
  hence "corres_underlying sr nf nf' r1 P P' 
               (do a \<leftarrow> A; b \<leftarrow> B; c \<leftarrow> C; d \<leftarrow> D; rv \<leftarrow> return (a, b, c, d); 
                   H (fst rv) (fst (snd rv)) (fst (snd (snd rv))) (snd (snd (snd rv))) od) 
               (do a' \<leftarrow> A'; b' \<leftarrow> B'; c' \<leftarrow> C'; d' \<leftarrow> D'; rv \<leftarrow> return (a', b', c', d'); 
                   H' (fst rv) (fst (snd rv)) (fst (snd (snd rv))) (snd (snd (snd rv))) od)"
    by (simp add: bind_assoc)
  thus ?thesis by simp
qed

(* for instantiations *)
lemma corres_inst: "corres_underlying sr nf nf' r P P' f g \<Longrightarrow> corres_underlying sr nf nf' r P P' f g" .

lemma corres_assert_opt_assume:
  assumes "\<And>x. P' = Some x \<Longrightarrow> corres_underlying sr nf nf' r P Q f (g x)"
  assumes "\<And>s. Q s \<Longrightarrow> P' \<noteq> None"
  shows "corres_underlying sr nf nf' r P Q f (assert_opt P' >>= g)" using assms
  by (auto simp: bind_def assert_opt_def assert_def fail_def return_def 
                 corres_underlying_def split: option.splits)
  

text {* Support for proving correspondance by decomposing the state relation *}

lemma corres_underlying_decomposition:
  assumes x: "corres_underlying {(s, s'). P s s'} nf nf' r Pr Pr' f g"
      and y: "\<And>s'. \<lbrace>R s'\<rbrace> f \<lbrace>\<lambda>rv s. Q s s'\<rbrace>"
      and z: "\<And>s. \<lbrace>P s and Q s and K (Pr s) and Pr'\<rbrace> g \<lbrace>\<lambda>rv s'. R s' s\<rbrace>"
  shows      "corres_underlying {(s, s'). P s s' \<and> Q s s'} nf nf' r Pr Pr' f g"
  using x apply (clarsimp simp: corres_underlying_def)
  apply (elim allE, drule(1) mp, clarsimp)
  apply (drule(1) bspec)
  apply clarsimp
  apply (rule rev_bexI, assumption)
  apply simp
  apply (erule use_valid [OF _ y])
  apply (erule use_valid [OF _ z])
  apply simp
  done



lemma corres_stronger_no_failI:
  assumes f': "nf' \<Longrightarrow> no_fail (\<lambda>s'. \<exists>s. P s \<and> (s,s') \<in> S \<and> P' s')  f'"
  assumes corres: "\<forall>(s, s') \<in> S. P s \<and> P' s' \<longrightarrow>
                     (\<forall>(r', t') \<in> fst (f' s'). \<exists>(r, t) \<in> fst (f s). (t, t') \<in> S \<and> R r (r', t'))"
  shows "corres_underlying S nf nf' R P P' f f'"
  using assms
  apply (simp add: corres_underlying_def no_fail_def)
  apply clarsimp
  apply (rule conjI)
   apply clarsimp
   apply blast
  apply clarsimp
  apply blast
  done

lemma corres_fail:
  assumes no_fail: "\<And>s s'. \<lbrakk> (s,s') \<in> sr; P s; P' s'; nf' \<rbrakk> \<Longrightarrow> False"
  shows "corres_underlying sr nf nf' R P P' f fail"
  using no_fail
  by (auto simp add: corres_underlying_def fail_def)

lemma corres_returnOk:
  "(\<And>s s'. \<lbrakk> (s,s') \<in> sr; P s; P' s' \<rbrakk> \<Longrightarrow> r x (y, s')) \<Longrightarrow>
  corres_underlying sr nf nf' (r' \<oplus> r) P P' (returnOk x) (returnOk y)"
  apply (rule corres_noopE)
   apply wp
   apply clarsimp
  apply (rule no_fail_pre, wp)
  done

lemmas corres_returnOkTT = corres_trivial [OF corres_returnOk]

lemma corres_False [simp]:
  "corres_underlying sr nf nf' r P \<bottom> f f'"
  by (simp add: corres_underlying_def)

lemma corres_liftME[simp]:
  "corres_underlying sr nf nf' (f \<oplus> r) P P' (liftME fn m) m'
   = corres_underlying sr nf nf' (f \<oplus> (r \<circ> fn)) P P' m m'"
  apply (simp add: liftME_liftM)
  apply (rule corres_cong [OF refl refl refl refl])
  apply (case_tac x, simp_all)
  done

lemma corres_liftME2[simp]:
  "corres_underlying sr nf nf' (f \<oplus> r) P P' m (liftME fn m')
   = corres_underlying sr nf nf' (f \<oplus> (\<lambda>x (y, s). r x (fn y, s))) P P' m m'"
  apply (simp add: liftME_liftM)
  apply (rule corres_cong [OF refl refl refl refl])
  apply (case_tac y, simp_all)
  done

lemma corres_assertE_assume:
  "\<lbrakk>\<And>s. P s \<longrightarrow> P'; \<And>s'. Q s' \<longrightarrow> Q'; \<And>s'. r () ((), s')\<rbrakk> \<Longrightarrow>
   corres_underlying sr nf nf' (f \<oplus> r) P Q (assertE P') (assertE Q')"
  by (auto simp add: corres_underlying_def assertE_def returnOk_def
                   fail_def return_def)

definition
  rel_prod :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'c \<Rightarrow> 'b \<times> 'd \<Rightarrow> bool)"
  (infix "\<otimes>" 97)
where
  "rel_prod \<equiv> \<lambda>f g (a,b) (c,d). f a c \<and> g b d"

lemma rel_prod_apply [simp]:
  "(f \<otimes> g) (a,b) (c,d) = (f a c \<and> g b d)"
  by (simp add: rel_prod_def)

lemma mapME_x_corres_inv:
  assumes x: "\<And>x. corres_underlying sr nf nf' (f \<oplus> dc) (P x) (P' x) (m x) (m' x)"
  assumes y: "\<And>x P. \<lbrace>P\<rbrace> m x \<lbrace>\<lambda>x. P\<rbrace>,-" "\<And>x P'. \<lbrace>P'\<rbrace> m' x \<lbrace>\<lambda>x. P'\<rbrace>,-"
  assumes z: "xs = ys"
  shows      "corres_underlying sr nf nf' (f \<oplus> dc) (\<lambda>s. \<forall>x \<in> set xs. P x s) (\<lambda>s. \<forall>y \<in> set ys. P' y s)
                              (mapME_x m xs) (mapME_x m' ys)"
  unfolding z
proof (induct ys)
  case Nil
  show ?case
    by (simp add: mapME_x_def sequenceE_x_def returnOk_def)
next
  case (Cons z zs)
    from Cons have IH:
      "corres_underlying sr nf nf' (f \<oplus> dc) (\<lambda>s. \<forall>x\<in>set zs. P x s) (\<lambda>s. \<forall>y\<in>set zs. P' y s)
                       (mapME_x m zs) (mapME_x m' zs)" .
  show ?case
    apply (simp add: mapME_x_def sequenceE_x_def)
    apply (fold mapME_x_def sequenceE_x_def dc_def)
    apply (rule corres_guard_imp)
      apply (rule corres_splitEE [where r'="dc" and P="P z"
          and Q="\<lambda>s. \<forall>x\<in>set zs. P x s" and P'="P' z"
          and Q'="\<lambda>s. \<forall>x\<in>set zs. P' x s"])
      using IH unfolding dc_def apply simp
      using x unfolding dc_def apply assumption
      apply simp_all
      using y unfolding validE_def validE_R_def valid_def apply auto
  done 
qed

lemma corres_cases:
  "\<lbrakk> R \<Longrightarrow> corres_underlying sr nf nf' r P P' f g; \<not>R \<Longrightarrow> corres_underlying sr nf nf' r Q Q' f g \<rbrakk>  
  \<Longrightarrow> corres_underlying sr nf nf' r (P and Q) (P' and Q') f g"
  by (simp add: corres_underlying_def) blast

lemma corres_alternate1:
  "corres_underlying sr nf nf' r P P' a c \<Longrightarrow> corres_underlying sr nf nf' r P P' (a \<sqinter> b) c"
  apply (simp add: corres_underlying_def alternative_def)
  apply clarsimp
  apply (drule (1) bspec, clarsimp)+
  apply (rule rev_bexI)
   apply (rule UnI1)
   apply assumption
  apply simp
  done

lemma corres_alternate2:
  "corres_underlying sr nf nf' r P P' b c \<Longrightarrow> corres_underlying sr nf nf' r P P' (a \<sqinter> b) c"
  apply (simp add: corres_underlying_def alternative_def)
  apply clarsimp
  apply (drule (1) bspec, clarsimp)+
  apply (rule rev_bexI)
   apply (rule UnI2)
   apply assumption
  apply simp
  done

lemma corres_False':
  "corres_underlying sr nf nf' r \<bottom> P' f g"
  by (simp add: corres_underlying_def)

lemma corres_symb_exec_l_Ex:
  assumes x: "\<And>rv. corres_underlying sr nf nf' r (Q rv) P' (g rv) h"
  shows      "corres_underlying sr nf nf' r (\<lambda>s. \<exists>rv. Q rv s \<and> (rv, s) \<in> fst (f s)) P'
                       (do rv \<leftarrow> f; g rv od) h"
  apply (clarsimp simp add: corres_underlying_def)
  apply (cut_tac rv=rv in x)
  apply (clarsimp simp add: corres_underlying_def)
  apply (drule(1) bspec, clarsimp)
  apply (case_tac nf)
   apply (clarsimp simp: bind_def')
   apply blast
  apply clarsimp
  apply (drule(1) bspec, clarsimp)
  apply (clarsimp simp: bind_def | erule rev_bexI)+
  done

lemma corres_symb_exec_r_All:
  assumes nf: "\<And>rv. nf' \<Longrightarrow> no_fail (Q' rv) g"
  assumes x: "\<And>rv. corres_underlying sr nf nf' r P (Q' rv) f (h rv)"
  shows      "corres_underlying sr nf nf' r P (\<lambda>s. (\<forall>p \<in> fst (g s). snd p = s \<and> Q' (fst p) s) \<and> (\<exists>rv. Q' rv s))
                       f (do rv \<leftarrow> g; h rv od)"
  apply (clarsimp simp add: corres_underlying_def bind_def)
  apply (rule conjI)
   apply clarsimp
   apply (cut_tac rv=aa in x)
   apply (clarsimp simp add: corres_underlying_def bind_def)
   apply (drule(1) bspec, clarsimp)+
  apply (insert nf)
  apply (clarsimp simp: no_fail_def)
  apply (erule (1) my_BallE)
  apply (cut_tac rv="aa" in x)
  apply (clarsimp simp add: corres_underlying_def bind_def)
  apply (drule(1) bspec, clarsimp)+
  done

lemma corres_split_bind_case_sum:
  assumes ad: "corres_underlying sr nf nf' (lr \<oplus> rr) P P' a d"
  assumes be: "\<And>rv rv'. corres_underlying sr nf nf' r (R rv) (\<lambda>s'. lr rv (rv', s') \<and> R' rv' s') (b rv) (e rv')"
  assumes cf: "\<And>rv rv'. corres_underlying sr nf nf' r (S rv) (\<lambda>s'. rr rv (rv', s') \<and> S' rv' s') (c rv) (f rv')"
  assumes valid: "\<lbrace>Q\<rbrace> a \<lbrace>S\<rbrace>,\<lbrace>R\<rbrace>" "\<lbrace>Q'\<rbrace> d \<lbrace>S'\<rbrace>,\<lbrace>R'\<rbrace>"
  shows "corres_underlying sr nf nf' r (P and Q) (P' and Q')
            (a >>= case_sum b c) (d >>= case_sum e f)"
proof (rule corres_split [where r'="lr \<oplus> rr" and R="case_sum R S" and R'="case_sum R' S'"])
  fix rv :: "'c + 'd" and rv' :: "'e + 'f"
  let ?goal = "corres_underlying sr nf nf' r (case_sum R S rv)
        (\<lambda>s'. (lr \<oplus> rr) rv (rv', s') \<and> case_sum R' S' rv' s') (case_sum b c rv) (case_sum e f rv')"
  { fix rvl :: "'c"
    assume "rv = Inl rvl"
    moreover hence "\<And>s'. (lr \<oplus> rr) rv (rv', s') \<Longrightarrow> \<exists>rvl'. rv' = Inl rvl'" by auto
    ultimately have ?goal
      using be
      apply -
      apply (rule corres_assume_pre, auto)
      done}
  moreover
  { fix rvr :: "'d"
    assume "rv = Inr rvr"
    moreover hence "\<And>s'. (lr \<oplus> rr) rv (rv', s') \<Longrightarrow> \<exists>rvr'. rv' = Inr rvr'" by auto
    ultimately have ?goal
      using cf
      apply -
      apply (rule corres_assume_pre, auto)
      done}
  ultimately show ?goal using sumE by blast
next
  from ad show "corres_underlying sr nf nf' (lr \<oplus> rr) P P' a d" .
next
  show "\<lbrace>Q\<rbrace> a \<lbrace>case_sum R S\<rbrace>" by (simp add: valid(1) validE_cases_valid)
next
  show "\<lbrace>Q'\<rbrace> d \<lbrace>case_sum R' S'\<rbrace>" by (simp add: valid(2) validE_cases_valid)
qed

lemma whenE_throwError_corres_initial:
  assumes P: "\<And>s'. frel f (f', s')"
  assumes Q: "P = P'"
  assumes R: "\<not> P \<Longrightarrow> corres_underlying sr nf nf' (frel \<oplus> rvr) Q Q' m m'"
  shows      "corres_underlying sr nf nf' (frel \<oplus> rvr) Q Q'
                     (whenE P  (throwError f ) >>=E (\<lambda>_. m ))
                     (whenE P' (throwError f') >>=E (\<lambda>_. m'))"
  unfolding whenE_def
  apply (cases P)
   apply (simp add: P Q)
  apply (simp add: Q)
  apply (rule R)
  apply (simp add: Q)
  done

lemma whenE_throwError_corres:
  assumes P: "\<And>s'. frel f (f', s')"
  assumes Q: "P = P'"
  assumes R: "\<not> P \<Longrightarrow> corres_underlying sr nf nf' (frel \<oplus> rvr) Q Q' m m'"
  shows      "corres_underlying sr nf nf' (frel \<oplus> rvr) (\<lambda>s. \<not> P \<longrightarrow> Q s) (\<lambda>s. \<not> P' \<longrightarrow> Q' s)
                     (whenE P  (throwError f ) >>=E (\<lambda>_. m ))
                     (whenE P' (throwError f') >>=E (\<lambda>_. m'))"
  apply (rule whenE_throwError_corres_initial)
  apply (simp_all add: P Q R)
  done

lemma corres_move_asm:
  "\<lbrakk> corres_underlying sr nf nf' r P  Q f g;
      \<And>s s'. \<lbrakk>(s,s') \<in> sr; P s; P' s'\<rbrakk> \<Longrightarrow> Q s'\<rbrakk>
    \<Longrightarrow> corres_underlying sr nf nf' r P P' f g"
  by (fastforce simp: corres_underlying_def)

lemma corres_weak_cong:
  "\<lbrakk>\<And>s. P s \<Longrightarrow> f s = f' s; \<And>s. Q s \<Longrightarrow> g s = g' s\<rbrakk>
  \<Longrightarrow> corres_underlying sr nf nf' r P Q f g = corres_underlying sr nf nf' r P Q f' g'"
  by (simp cong: corres_cong)

lemma corres_either_alternate:
  "\<lbrakk> corres_underlying sr nf nf' r P Pa' a c; corres_underlying sr nf nf' r P Pb' b c \<rbrakk>
   \<Longrightarrow> corres_underlying sr nf nf' r P (Pa' or Pb') (a \<sqinter> b) c"
  apply (simp add: corres_underlying_def alternative_def)
  apply clarsimp
  apply (drule (1) bspec, clarsimp)+
  apply (erule disjE, clarsimp)
   apply (drule(1) bspec, clarsimp)
   apply (rule rev_bexI)
    apply (erule UnI1)
   apply simp
  apply (clarsimp, drule(1) bspec, clarsimp)
  apply (rule rev_bexI)
   apply (erule UnI2)
  apply simp
  done

lemma corres_either_alternate2:
  "\<lbrakk> corres_underlying sr nf nf' r P R a c; corres_underlying sr nf nf' r Q R b c \<rbrakk>
   \<Longrightarrow> corres_underlying sr nf nf' r (P or Q) R (a \<sqinter> b) c"
  apply (simp add: corres_underlying_def alternative_def)
  apply clarsimp
  apply (drule (1) bspec, clarsimp)+
   apply (erule disjE)
   apply clarsimp
   apply (drule(1) bspec, clarsimp)
   apply (rule rev_bexI)
    apply (erule UnI1)
   apply simp
   apply clarsimp
  apply (drule(1) bspec, clarsimp)
  apply (rule rev_bexI)
   apply (erule UnI2)
  apply simp
  done

lemma option_corres:
  assumes "x = None \<Longrightarrow> corres_underlying sr nf nf' r P P' (A None) (C None)"
  assumes "\<And>z. x = Some z \<Longrightarrow> corres_underlying sr nf nf' r (Q z) (Q' z) (A (Some z)) (C (Some z))"
  shows "corres_underlying sr nf nf' r (\<lambda>s. (x = None \<longrightarrow> P s) \<and> (\<forall>z. x = Some z \<longrightarrow> Q z s)) 
                  (\<lambda>s. (x = None \<longrightarrow> P' s) \<and> (\<forall>z. x = Some z \<longrightarrow> Q' z s)) 
                  (A x) (C x)"
  by (cases x) (auto simp: assms)

lemma corres_bind_return:
 "corres_underlying sr nf nf' r P P' (f >>= return) g \<Longrightarrow>
  corres_underlying sr nf nf' r P P' f g"
  by (simp add: corres_underlying_def)

lemma corres_bind_return2:
  "corres_underlying sr nf nf' r P P' f (g >>= return) \<Longrightarrow> corres_underlying sr nf nf' r P P' f g"
  by simp

lemma corres_stateAssert_implied2:
  assumes c: "corres_underlying sr nf nf' r P Q f g"
  assumes sr: "\<And>s s'. \<lbrakk>(s, s') \<in> sr; R s; R' s'\<rbrakk> \<Longrightarrow> Q' s'"
  assumes f: "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. R\<rbrace>"
  assumes g: "\<lbrace>Q\<rbrace> g \<lbrace>\<lambda>_. R'\<rbrace>"
  shows "corres_underlying sr nf nf' dc P Q f (g >>= (\<lambda>_. stateAssert Q' []))"
  apply (subst bind_return[symmetric])
  apply (rule corres_guard_imp)
    apply (rule corres_split)
       prefer 2
       apply (rule c)
      apply (clarsimp simp: corres_underlying_def return_def 
                            stateAssert_def bind_def get_def assert_def
                            fail_def)
      apply (drule (2) sr)
      apply simp
     apply (rule f)
    apply (rule g)
   apply simp
  apply simp
  done

lemma corres_add_noop_lhs:
  "corres_underlying sr nf nf' r P P' (return () >>= (\<lambda>_. f)) g
      \<Longrightarrow> corres_underlying sr nf nf' r P P' f g"
  by simp

lemma corres_add_noop_lhs2:
  "corres_underlying sr nf nf' r P P' (f >>= (\<lambda>_. return ())) g
      \<Longrightarrow> corres_underlying sr nf nf' r P P' f g"
  by simp

lemmas corres_split_noop_rhs
  = corres_split_nor[THEN corres_add_noop_lhs, OF _ _ return_wp]

lemmas corres_split_noop_rhs2
  = corres_split_nor[THEN corres_add_noop_lhs2]

lemma isLeft_case_sum:
  "isLeft v \<Longrightarrow> (case v of Inl v' \<Rightarrow> f v' | Inr v' \<Rightarrow> g v') = f (theLeft v)"
  by (clarsimp simp: isLeft_def)

lemma corres_symb_exec_catch_r:
  "\<lbrakk> \<And>rv. corres_underlying sr nf nf' r P (Q' rv) f (h rv);
        \<lbrace>P'\<rbrace> g \<lbrace>\<bottom>\<bottom>\<rbrace>, \<lbrace>Q'\<rbrace>; \<And>s\<^sub>A. \<lbrace>\<lambda>s\<^sub>C. P' s\<^sub>C \<and> (s\<^sub>A, s\<^sub>C) \<in> sr\<rbrace> g \<lbrace>\<lambda>r s\<^sub>C. (s\<^sub>A, s\<^sub>C) \<in> sr\<rbrace>;
        nf' \<Longrightarrow> no_fail P' g \<rbrakk>
      \<Longrightarrow> corres_underlying sr nf nf' r P P' f (g <catch> h)"
  apply (simp add: catch_def)
  apply (rule corres_symb_exec_r, simp_all)
   apply (rule_tac F="isLeft rv" in corres_gen_asm2)
   apply (simp add: isLeft_case_sum)
   apply assumption
  apply (simp add: validE_def)
  apply (erule hoare_chain, simp_all)[1]
  apply (simp add: isLeft_def split: sum.split_asm)
  done

end