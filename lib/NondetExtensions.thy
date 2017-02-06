theory NondetExtensions
imports
  SimpleSimulation
  AutoCorres
begin

definition
  lift_nd :: "('a, 'r) nondet_monad \<Rightarrow> ('a \<times> 'a) set"
where
  "lift_nd m \<equiv> { (s, s'). \<exists>r. (r, s') \<in> fst (m s) }"

definition
  invariant_holds_nd :: "('a, 'b) data_type \<Rightarrow> 'a set \<Rightarrow> ('a, 'r) nondet_monad \<Rightarrow> bool"
where
  "invariant_holds_nd A I m\<^sub>A \<equiv> (\<forall>s. Init A s \<subseteq> I)
    \<and> (Run A = lift_nd m\<^sub>A) \<and> \<lbrace>\<lambda>s. s \<in> I\<rbrace> m\<^sub>A \<lbrace>\<lambda>_ s'. s' \<in> I\<rbrace>"

lemma invariant_nd[dest]: "invariant_holds_nd A I m\<^sub>A \<Longrightarrow> A \<Turnstile> I"
unfolding invariant_holds_nd_def SimpleSimulation.invariant_holds_def lift_nd_def valid_def
by blast

end