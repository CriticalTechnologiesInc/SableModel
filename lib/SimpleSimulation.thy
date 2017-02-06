chapter {* Define processes that are linear in execution *}

theory SimpleSimulation
imports Main
begin

record ('a, 'b) data_type =
  Init :: "'b \<Rightarrow> 'a set"
  Fin :: "'a \<Rightarrow> 'b"
  Run :: "('a \<times> 'a) set"

text {*
We follow a simple strategy that allows us to use as much of the NICTA seL4 libraries as
possible. First, we define linear versions of constructs (e.g. the Hoare triple) in terms
of the more complex NICTA constructs. Then we prove simple introduction lemmas which allow us
to reason about linear constructs using lemmas defined over NICTA constructs. 
*}
definition execution where
"execution A \<equiv> \<lambda>s. Fin A ` (Run A `` Init A s)"

definition hoare_triple where
"hoare_triple A P Q \<equiv> \<forall>s s'. s \<in> P \<longrightarrow> s' \<in> execution A s \<longrightarrow> s' \<in> Q"

definition
  refines :: "('c,'b) data_type \<Rightarrow> ('a,'b) data_type \<Rightarrow> bool" (infix "\<sqsubseteq>" 60)
where
  "C \<sqsubseteq> A \<equiv> \<forall>s. execution C s \<subseteq> execution A s"

lemma hoare_triple_refinement:
  "C \<sqsubseteq> A = (\<forall>P Q. hoare_triple A P Q \<longrightarrow> hoare_triple C P Q)"
  by (simp add: refines_def hoare_triple_def) blast

definition
  rel_semi :: "('a \<times> 'b) set \<Rightarrow> ('b \<times> 'c) set \<Rightarrow> ('a \<times> 'c) set" (infixl ";;;" 65) 
where
  "A ;;; B \<equiv> A O B"

definition
  fw_sim :: "('a \<times> 'c) set \<Rightarrow> ('c,'b) data_type \<Rightarrow> ('a,'b) data_type \<Rightarrow> bool"
where
  "fw_sim R C A \<equiv> (\<forall>s. Init C s \<subseteq> R `` Init A s) \<and> 
                  (R ;;; Run C \<subseteq> Run A ;;; R) \<and>
                  (\<forall>s s'. (s,s') \<in> R \<longrightarrow> Fin C s' = Fin A s)"

definition
  fw_simulates :: "('c,'b) data_type \<Rightarrow> ('a,'b) data_type \<Rightarrow> bool" (infixl "\<sqsubseteq>\<^sub>F" 50)
where
  "C \<sqsubseteq>\<^sub>F A \<equiv> \<exists>R. fw_sim R C A"

lemma sim_imp_refines:
  fixes C :: "('c,'b) data_type" and A :: "('a,'b) data_type"
  assumes "C \<sqsubseteq>\<^sub>F A"
  shows "C \<sqsubseteq> A"
proof -
  from assms have "\<exists>R. fw_sim R C A" unfolding fw_simulates_def .
  then obtain R where "fw_sim R C A" ..
  hence init: "\<forall>s. Init C s \<subseteq> R `` Init A s"
    and run:  "R ;;; Run C \<subseteq> Run A ;;; R"
    and fin:  "\<forall>s s'. (s,s') \<in> R \<longrightarrow> Fin C s' = Fin A s"
      unfolding fw_sim_def by auto
  have "\<forall>s. execution C s \<subseteq> execution A s"
  proof (safe)
    fix s s'
    assume "s' \<in> execution C s"
    hence "s' \<in> Fin C ` (Run C `` Init C s)" unfolding execution_def .
    hence "\<exists>s\<^sub>C' \<in> (Run C `` Init C s). s' = Fin C s\<^sub>C'" by auto
    then obtain s\<^sub>C' where "s\<^sub>C' \<in> (Run C `` Init C s)" and "s' = Fin C s\<^sub>C'" ..
    hence "\<exists>s\<^sub>C \<in> Init C s. (s\<^sub>C, s\<^sub>C') \<in> Run C" by auto
    then obtain s\<^sub>C where "s\<^sub>C \<in> Init C s" and "(s\<^sub>C, s\<^sub>C') \<in> Run C" ..
    with init have "s\<^sub>C \<in> R `` Init A s" by auto
    hence "\<exists>s\<^sub>A \<in> Init A s. (s\<^sub>A, s\<^sub>C) \<in> R" by auto
    then obtain s\<^sub>A where "s\<^sub>A \<in> Init A s" and "(s\<^sub>A, s\<^sub>C) \<in> R" ..
    with `(s\<^sub>C, s\<^sub>C') \<in> Run C` have "(s\<^sub>A, s\<^sub>C') \<in> R ;;; Run C" unfolding rel_semi_def by auto
    with run have "(s\<^sub>A, s\<^sub>C') \<in> Run A ;;; R" by auto
    hence "\<exists>s\<^sub>A'. (s\<^sub>A, s\<^sub>A') \<in> Run A \<and> (s\<^sub>A', s\<^sub>C') \<in> R" unfolding rel_semi_def by auto
    then obtain s\<^sub>A' where "(s\<^sub>A, s\<^sub>A') \<in> Run A" and "(s\<^sub>A', s\<^sub>C') \<in> R" by auto
    with fin and `s' = Fin C s\<^sub>C'` have "s' = Fin A s\<^sub>A'" by auto
    with `s\<^sub>A \<in> Init A s` and `(s\<^sub>A, s\<^sub>A') \<in> Run A` have "s' \<in> Fin A ` (Run A `` Init A s)" by auto
    thus "s' \<in> execution A s" unfolding execution_def .
  qed
  thus "C \<sqsubseteq> A" unfolding refines_def .
qed

definition
  invariant_holds :: "('a,'b) data_type \<Rightarrow> 'a set \<Rightarrow> bool" (infix "\<Turnstile>" 60)
where
  "invariant_holds A I \<equiv> (\<forall>s. Init A s \<subseteq> I) \<and> (Run A `` I \<subseteq> I)"

lemma invariant_T [iff]: "D \<Turnstile> UNIV"
  by (simp add: invariant_holds_def)

lemma invariantI:
  "\<lbrakk> \<forall>s. Init D s \<subseteq> I; Run D `` I \<subseteq> I \<rbrakk> \<Longrightarrow> D \<Turnstile> I"
by (simp add: invariant_holds_def)

lemma invariant_CollectI [intro?]:
  assumes init: "\<And>s a. s \<in> Init D a \<Longrightarrow> I s"
  assumes step: "\<And>s s'. \<lbrakk> I s; (s,s') \<in> Run D \<rbrakk> \<Longrightarrow> I s'"
  shows "D \<Turnstile> Collect I"
proof (rule invariantI)
  show "\<forall>a. Init D a \<subseteq> Collect I" by (fast intro: init)
next
  show "Run D `` Collect I \<subseteq> Collect I"
    by (auto simp add: Image_def intro: step)
qed

lemma invariant_conjI:
  "D \<Turnstile> P \<Longrightarrow> D \<Turnstile> Q  \<Longrightarrow> D \<Turnstile> P \<inter> Q"
  by (simp add: invariant_holds_def) blast

lemma invariant_conjI2:
  "\<lbrakk> D \<Turnstile> I; \<And>s. Init D s \<subseteq> I \<Longrightarrow> Init D s \<subseteq> J; 
    Run D `` (I \<inter> J) \<subseteq> J \<rbrakk> \<Longrightarrow> D \<Turnstile> I \<inter> J"    
  by (simp add: invariant_holds_def) blast

definition
  LI :: "('a,'b) data_type \<Rightarrow> ('c,'b) data_type \<Rightarrow> ('a \<times> 'c) set \<Rightarrow> ('a \<times> 'c) set \<Rightarrow> bool"
where
  "LI A C R I \<equiv> (\<forall>s. Init C s \<subseteq> R `` Init A s) \<and> 
                ((R \<inter> I) ;;; Run C \<subseteq> Run A ;;; R) \<and>
                (\<forall>s s'. (s,s') \<in> R \<inter> I \<longrightarrow> Fin C s' = Fin A s)"
(* Arash *)
lemma LI_fw_sim:
  fixes C :: "('c,'b) data_type" and A :: "('a,'b) data_type" and R I\<^sub>A I\<^sub>C 
  assumes ia: "A \<Turnstile> I\<^sub>a" and ic: "C \<Turnstile> I\<^sub>c" and li: "LI A C R (I\<^sub>a \<times> I\<^sub>c)"
  shows "fw_sim (R \<inter> I\<^sub>a \<times> I\<^sub>c) C A"
apply (simp add:fw_sim_def) 
proof (rule  conjI)
  show "\<forall>s. Init C s \<subseteq> (R \<inter> I\<^sub>a \<times> I\<^sub>c) `` Init A s"
  proof 
    fix s
    from li have 0 : "Init C s \<subseteq> R `` Init A s" unfolding LI_def by auto
    show "Init C s \<subseteq> (R \<inter> I\<^sub>a \<times> I\<^sub>c) `` Init A s"
    proof
      fix c
      assume "c \<in> Init C s"
      from this and ic have "c \<in> I\<^sub>c" unfolding invariant_holds_def by auto
      from `c \<in> Init C s` and 0 have "c \<in> (R `` Init A s)" by auto
      then have "\<exists> a. a \<in> Init A s \<and> (a,c) \<in> R" by auto
      then obtain a where aCond:"a \<in> Init A s \<and> (a,c) \<in> R" by auto
      then have "a \<in> I\<^sub>a" using ia unfolding invariant_holds_def by auto
      then have "(a,c) \<in> R \<inter>(I\<^sub>a \<times> I\<^sub>c)" using `c \<in> I\<^sub>c` and aCond by blast
      then show "c \<in> (R \<inter> I\<^sub>a \<times> I\<^sub>c) `` Init A s" using aCond by blast
    qed
  qed
next
   show "R \<inter> I\<^sub>a \<times> I\<^sub>c ;;; Run C \<subseteq> Run A ;;; R \<inter> I\<^sub>a \<times> I\<^sub>c \<and>
    (\<forall>s s'. (s, s') \<in> R \<and> s \<in> I\<^sub>a \<and> s' \<in> I\<^sub>c \<longrightarrow> Fin C s' = Fin A s)"
    proof(safe)
      fix a c 
      assume 0:"(a,c) \<in>  R \<inter> I\<^sub>a \<times> I\<^sub>c ;;; Run C"
      from ia have iaa: "(s,s') \<in> Run A \<Longrightarrow> s \<in> I\<^sub>a  \<Longrightarrow> s' \<in> I\<^sub>a" 
        by (auto simp: invariant_holds_def)
      from ic have icc: "(xx,xx') \<in> Run C \<Longrightarrow> xx \<in> I\<^sub>c  \<Longrightarrow> xx' \<in> I\<^sub>c"
        by (auto simp: invariant_holds_def)
      from 0 have aIa: "a \<in> I\<^sub>a" unfolding rel_semi_def by auto
      from 0 have cIc: "c \<in> I\<^sub>c" using ic  unfolding rel_semi_def
      proof -
        assume "(a,c) \<in> (R \<inter> I\<^sub>a \<times> I\<^sub>c) O Run C"
        then have "\<exists> cc. (a,cc) \<in>  R \<inter> I\<^sub>a \<times> I\<^sub>c \<and> (cc,c) \<in> Run C" using 0  by blast
        then obtain cc where ccCond:"(a,cc) \<in>  R \<inter> I\<^sub>a \<times> I\<^sub>c \<and> (cc,c) \<in> Run C" by auto
        then have "cc \<in> I\<^sub>c" by auto
        then show "c \<in> I\<^sub>c" using ccCond ic unfolding invariant_holds_def by auto
      qed
      have 1: "(a,c) \<in> Run A ;;; R"
      proof -
        from li have "R \<inter> I\<^sub>a \<times> I\<^sub>c ;;; Run C \<subseteq> Run A ;;; R" unfolding LI_def by auto
        then show ?thesis using 0 by blast
      qed
      from 1 have "\<exists> b . (a,b) \<in> Run A \<and> (b,c) \<in> R" unfolding rel_semi_def by auto
      then obtain b where bCon: "(a,b) \<in> Run A \<and> (b,c) \<in> R" ..
      from this and aIa and iaa have bIa: "b \<in> I\<^sub>a" 
        by (meson ImageI ia invariant_holds_def subsetCE) 
      from bCon have "(b,c) \<in> R" by auto
      from this and cIc and bIa have "(b,c) \<in> R \<inter> (I\<^sub>a \<times> I\<^sub>c)" by blast
      from bCon have "(a,b) \<in> Run A" by auto
      from this and `(b,c) \<in> R \<inter> (I\<^sub>a \<times> I\<^sub>c)` have "(a,c) \<in> Run A ;;; R \<inter> (I\<^sub>a \<times> I\<^sub>c)" 
        by (auto simp: rel_semi_def)
      from this show "(a,c) \<in> Run A ;;; R \<inter> (I\<^sub>a \<times> I\<^sub>c)" by auto
    next
      fix s s'
      assume "(s,s') \<in> R" and "s \<in> I\<^sub>a" and  "s' \<in> I\<^sub>c"
      from this and li have "(s,s') \<in> R \<inter> (I\<^sub>a \<times> I\<^sub>c)" by auto
      from this and li show  "Fin C s' = Fin A s" by (simp add: LI_def)
   qed
qed

 (* Arash *)     
lemma weaken_LI:
  fixes C :: "('c,'b) data_type" and A :: "('a,'b) data_type" and R I I'
  assumes LI: "LI A C R I'" and weaker: "I \<subseteq> I'"
  shows "LI A C R I"
apply(simp_all add: LI_def)
proof
  show "\<forall>s. Init C s \<subseteq> R `` Init A s" using LI unfolding LI_def by auto
  next show " R \<inter> I ;;; Run C \<subseteq> Run A ;;; R \<and>
    (\<forall>s s'. (s, s') \<in> R \<and> (s, s') \<in> I \<longrightarrow> Fin C s' = Fin A s)"
  proof (safe)
    fix a c
    assume "(a,c) \<in> R \<inter> I ;;; Run C"
    then have "\<exists> b. (a,b) \<in> R \<inter> I \<and> (b,c) \<in> Run C" unfolding rel_semi_def by auto
    then obtain b where bCond:"(a,b) \<in> R \<inter> I \<and> (b,c) \<in> Run C" by auto
    then have "(a,b) \<in> R \<inter> I'" using weaker by auto
    then have "(a,c) \<in> R \<inter> I' ;;; Run C" using bCond by (auto simp:rel_semi_def)
    then show "(a,c) \<in> Run A;;; R" using LI unfolding LI_def by auto
    next
    fix s s'
    assume "(s,s') \<in> R" and "(s,s') \<in> I"
    then have "(s,s') \<in> I'" using weaker by auto
    then have "(s,s') \<in> R \<inter> I'" using `(s,s') \<in> R` by auto
    then show "Fin C s' = Fin A s" using LI unfolding LI_def by auto
  qed
qed 

lemma fw_sim_eq_LI: "fw_sim r C A = LI A C r UNIV"
unfolding fw_sim_def LI_def by simp

lemma fw_sim_LI: "fw_sim r C A \<Longrightarrow> LI A C r I"
by (simp add: fw_sim_eq_LI weaken_LI[where I'=UNIV])

lemma L_invariantI:
  assumes  "A \<Turnstile> I\<^sub>a" and "C \<Turnstile> I\<^sub>c" and "LI A C r (I\<^sub>a \<times> I\<^sub>c)"
  shows "C \<sqsubseteq>\<^sub>F A"
  using assms
  by (simp add: fw_simulates_def, rule_tac x="r \<inter> I\<^sub>a \<times> I\<^sub>c" in exI,
      simp add: LI_fw_sim)

lemma refinement_refl[simp]: "A \<sqsubseteq> A"
unfolding refines_def by auto

lemma refinement_trans [trans]: "\<lbrakk>C \<sqsubseteq> B; B \<sqsubseteq> A\<rbrakk> \<Longrightarrow> C \<sqsubseteq> A"
unfolding refines_def by auto

(* Arash *)
lemma fw_inv_transport2:
  fixes A I\<^sub>a C I\<^sub>c R
  assumes "A \<Turnstile> I\<^sub>a" and  "C \<Turnstile> I\<^sub>c" and li:"LI A C R (I\<^sub>a \<times> I\<^sub>c)"
  shows "C \<Turnstile> {s'. \<exists>s. (s,s') \<in> R \<and> s \<in> I\<^sub>a \<and> s' \<in> I\<^sub>c}"
apply(simp add:invariant_holds_def)
proof  
  show "\<forall>s. Init C s \<subseteq> {s'. \<exists>s. (s, s') \<in> R \<and> s \<in> I\<^sub>a \<and> s' \<in> I\<^sub>c}"
  proof
    fix s
    show "Init C s \<subseteq> {s'. \<exists>s. (s, s') \<in> R \<and> s \<in> I\<^sub>a \<and> s' \<in> I\<^sub>c}"
    proof
      fix x
      assume "x \<in> Init C s"
      then have "x \<in> R `` Init A s" using li unfolding LI_def by auto
      then have "\<exists> s' . s' \<in> Init A s \<and> (s',x) \<in> R" by auto
      then obtain s' where c1:"s' \<in> Init A s \<and> (s',x) \<in> R" by auto
      then have c2:"s' \<in> I\<^sub>a" using `A \<Turnstile> I\<^sub>a` unfolding invariant_holds_def by auto
      from `C \<Turnstile> I\<^sub>c`` x \<in> Init C s`  have c3: "x \<in> I\<^sub>c" unfolding invariant_holds_def by auto
      then have "(s', x) \<in> R \<and> s' \<in> I\<^sub>a \<and> x \<in> I\<^sub>c" using c1 c2 by auto
      then show "x \<in> {xx . \<exists>s' . (s',xx) \<in> R \<and> s' \<in> I\<^sub>a \<and> xx \<in> I\<^sub>c}" by auto
    qed
  qed
next
  let ?X = "{s'. \<exists>s. (s, s') \<in> R \<and> s \<in> I\<^sub>a \<and> s' \<in> I\<^sub>c}"
  show "Run C `` ?X \<subseteq> ?X"
  proof
  fix b
    assume "b \<in> Run C `` ?X"
    then have "\<exists> a. a \<in> ?X \<and> (a,b) \<in> Run C" by auto
    then obtain a where 0:"a \<in> ?X \<and> (a,b) \<in> Run C" by auto
    then have "\<exists> s . (s,a) \<in> R \<and> s \<in> I\<^sub>a \<and> a \<in> I\<^sub>c" by auto
    then obtain s where 1:"(s,a) \<in> R \<and> s \<in> I\<^sub>a \<and> a \<in> I\<^sub>c" by auto
    then have "(s,a) \<in> R \<inter> (I\<^sub>a\<times>I\<^sub>c)" by blast
    then have "(s,b) \<in> R \<inter> (I\<^sub>a\<times>I\<^sub>c) ;;; Run C" using 0 unfolding rel_semi_def  by blast
    then have "(s,b) \<in> Run A ;;; R" using li unfolding LI_def by blast
    then have "\<exists> ss. (s,ss) \<in> Run A \<and> (ss,b) \<in> R" unfolding rel_semi_def  by blast
    then obtain ss where 2:"(s,ss) \<in> Run A \<and> (ss,b) \<in> R" by auto
    from 1 have "s \<in> I\<^sub>a" by auto
    then have "ss \<in> I\<^sub>a" using 2 `A \<Turnstile> I\<^sub>a` unfolding invariant_holds_def by blast
    from 0 1 `C \<Turnstile> I\<^sub>c` have "b \<in> I\<^sub>c" unfolding invariant_holds_def by blast
    from 2 `ss \<in> I\<^sub>a` `b \<in> I\<^sub>c` have "(ss,b) \<in> R \<and> ss \<in> I\<^sub>a \<and> b \<in> I\<^sub>c" by auto
    then show "b \<in> ?X" by auto
  qed
qed

lemma fw_inv_transport:
  "\<lbrakk> A \<Turnstile> I\<^sub>a; C \<Turnstile> I\<^sub>c; LI A C R (I\<^sub>a \<times> I\<^sub>c) \<rbrakk> \<Longrightarrow> C \<Turnstile> {s'. \<exists>s. (s,s') \<in> R \<and> s \<in> I\<^sub>a \<and> s' \<in> I\<^sub>c}"
by (simp add: fw_inv_transport2)

lemma fw_sim_refl: "fw_sim Id A A"
unfolding fw_sim_def rel_semi_def by simp

lemma fw_simulates_refl[simp]: "A \<sqsubseteq>\<^sub>F A"
unfolding fw_simulates_def by (blast intro: fw_sim_refl)

lemma nondet_app_sub : "X \<subseteq> Y \<Longrightarrow> R `` X \<subseteq> R `` Y" by auto
lemma comp_sub : " X \<subseteq> Y \<Longrightarrow> R O X \<subseteq> R O Y" by auto
lemma comp_sub2 : "X \<subseteq> Y \<Longrightarrow>  X O R \<subseteq> Y O R" by auto
lemma comp_ass : "R1 O (R2 O R3) = (R1 O R2) O R3" by auto
lemma nondet_app_com : "R1``(R2`` X) = (R2 O R1) `` X"  by auto

(* Arash *)
lemma fw_sim_trans2:
  assumes fwsr1cb:"fw_sim R1 C B" and fwsr2ba:"fw_sim R2 B A"
  shows "fw_sim (R2 O R1) C A"
proof -
  let ?R = "R2 O R1"
  have init:"\<forall>s. Init C s \<subseteq> ?R `` Init A s"
  proof
    fix s
    have initCB:"Init C s \<subseteq> R1 `` Init B s" using fwsr1cb unfolding fw_sim_def by auto
    have initBA:"Init B s \<subseteq> R2 `` Init A s" using fwsr2ba unfolding fw_sim_def by auto
    then have "R1 `` Init B s \<subseteq> R1 `` (R2 `` Init A s)" using nondet_app_sub by auto
    then have "Init C s \<subseteq> R1 `` (R2 `` Init A s)" using initCB by auto
    then show "Init C s \<subseteq> (R2 O R1) `` Init A s" using nondet_app_com by force
  qed
  have run:"?R ;;; Run C \<subseteq> Run A ;;; ?R"
  proof -
    have runCB: "R1 O Run C \<subseteq> Run B O R1" using fwsr1cb unfolding fw_sim_def rel_semi_def by auto
    have runBA: "R2 O Run B \<subseteq> Run A O R2" using fwsr2ba unfolding fw_sim_def rel_semi_def by auto
    have 0: "R2 O R1 O Run C \<subseteq> R2 O Run B O R1" using runCB by blast
    have "R2 O Run B O R1 \<subseteq> Run A O R2 O R1" using runBA by blast
    then have "R2 O R1 O Run C \<subseteq> Run A O R2 O R1" using 0 by blast
    then show "(R2 O R1) ;;; Run C \<subseteq> Run A ;;; (R2 O R1)" unfolding rel_semi_def by blast
  qed
  have fin:"(\<forall>s s'. (s, s') \<in> ?R \<longrightarrow> Fin C s' = Fin A s)"
  proof (safe)
    fix s s' x y z
    show "(x, y) \<in> R2 \<Longrightarrow> (y,z) \<in> R1 \<Longrightarrow> Fin C z = Fin A x"
    proof -
      assume xyr2:"(x, y) \<in> R2" and "(y,z) \<in> R1"
      then have 0:"Fin C z = Fin B y" using fwsr1cb unfolding fw_sim_def by auto
      have "Fin B y = Fin A x" using fwsr2ba xyr2 unfolding fw_sim_def by auto
      then show "Fin C z = Fin A x" using 0 by auto
    qed
  qed
  from init run fin show "fw_sim ?R C A" using fw_sim_def by blast
qed

lemma fw_sim_trans: "\<lbrakk>fw_sim Q C B; fw_sim R B A\<rbrakk> \<Longrightarrow> fw_sim (R O Q) C A"
by (simp add:fw_sim_trans2)

lemma fw_simulates_trans: "\<lbrakk>C \<sqsubseteq>\<^sub>F B; B \<sqsubseteq>\<^sub>F A\<rbrakk> \<Longrightarrow> C \<sqsubseteq>\<^sub>F A"
unfolding fw_simulates_def by (blast dest: fw_sim_trans)

end