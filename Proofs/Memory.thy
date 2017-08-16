theory Memory
  imports
    "../AutoCorres/Impl"
    "../lib/ExtraLemmas"
    "./Memory_Nodes"
    "~/Isabelle2016-1/src/HOL/Library/LaTeXsugar"
    
begin
  
context sable_isa
begin
  
abbreviation "ALIGN_BITS \<equiv> 3"
abbreviation "OCC_FLG \<equiv> MEM_NODE_OCCUPIED_FLAG" 
  
abbreviation unat_ptr :: "'a ptr \<Rightarrow> nat"
  where "unat_ptr p \<equiv> unat (ptr_val p)"
    
definition
  mem_node_C_guard :: "mem_node_C ptr \<Rightarrow> bool"
  where
    "mem_node_C_guard n \<equiv> c_null_guard n \<and> is_aligned (ptr_val n) ALIGN_BITS"
    
lemma[dest, intro]: "mem_node_C_guard p \<Longrightarrow> c_guard p"
  unfolding mem_node_C_guard_def c_guard_def ptr_aligned_def is_aligned_def
  by (auto simp add: align_of_def, unat_arith)
    
lemma contrapos: "(P \<longrightarrow> Q) = (\<not>Q \<longrightarrow> \<not>P)"
  by blast
    
definition
  liftC :: "('c \<Rightarrow> 'a) \<Rightarrow> ('c \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)"
  where
    "liftC st P \<equiv> \<lambda>s. \<forall>g. s = st g \<longrightarrow> P g"
    
lemma hoare_liftC_wp[wp]:
  "\<lbrace>P\<rbrace> m \<lbrace>\<lambda>r s. \<forall>t. st s = t \<longrightarrow> Q r t\<rbrace> \<Longrightarrow> \<lbrace>liftC st P\<rbrace> exec_concrete st m \<lbrace>Q\<rbrace>"
  unfolding liftC_def
  apply wp
  unfolding valid_def
   apply auto 
  oops
    
lemma hoare_liftC[intro]:
  "\<lbrace>P\<rbrace> m \<lbrace>\<lambda>r s. \<forall>t. st s = t \<longrightarrow> liftC st (Q r) t\<rbrace> \<Longrightarrow>
   \<lbrace>liftC st P\<rbrace> exec_concrete st m \<lbrace>\<lambda>r s. liftC st (Q r) s\<rbrace>"
  apply wp
  sorry   
    
lemma fail'_wp: "\<lbrace>\<lambda>x. True\<rbrace> fail' \<lbrace>Q\<rbrace>"
  unfolding fail'_def FUNCTION_BODY_NOT_IN_INPUT_C_FILE_def by wp
    
    
    (*definition
  init_heap_P :: "unit ptr \<Rightarrow> 32 word \<Rightarrow> globals \<Rightarrow> bool"
where
  "init_heap_P p n s \<equiv> 0 \<notin> {ptr_val p..+unat n} \<and> is_aligned (ptr_val p) ALIGN_BITS \<and>
    (\<forall>node \<in> {ptr_val p..+unat n}. snd (hrs_htd (t_hrs_' s) node) = Map.empty)"*)
    
    (* FIXME move it out of here *)
lemma unat_add_le: "unat (a + b) \<le> unat (a::('a::len word)) + unat b "
  by unat_arith
    
definition nodeFree :: "globals \<Rightarrow> mem_node_C ptr \<Rightarrow> bool"
  where "nodeFree s node \<equiv>
    (let size = node_size_masked s node in
    \<forall>p \<in> {ptr_val (node +\<^sub>p 1)..+unat size * size_of TYPE(mem_node_C)}.
      snd (hrs_htd (t_hrs_' s) p) = Map.empty)"
    
lemma eight_eq_eight : "unat (8::32 word) = 8" by simp
    
definition nodeValid :: "globals \<Rightarrow> mem_node_C ptr \<Rightarrow> bool"
  where "nodeValid s node = 
  (let occupied = node_size s node && scast OCC_FLG in
   let next = node_next s node in
   let size = node_size_masked s node in
   c_guard node \<and> 
   unat_ptr node + 8 + unat (size * 8) \<le> 
    (if (next \<noteq> NULL) then unat_ptr next else 2 ^ LENGTH(32)) \<and>
   unat size * 8 < 2 ^ LENGTH(32) \<and>
   (occupied = 0 \<longrightarrow> nodeFree s node) \<and> 
   (next \<noteq> NULL \<longrightarrow> next > node \<and> next \<ge> (node +\<^sub>p 1)) )"
    
lemma "c_null_guard p \<Longrightarrow> 
  x \<in> ptr_span (p::mem_node_C ptr) \<Longrightarrow>
  unat x < unat_ptr p + size_of (TYPE(mem_node_C))" sorry 

lemma nodeValid_node_size_l1:
  "nodeValid s node \<Longrightarrow>  unat_ptr (node +\<^sub>p 1) + unat ((node_size_masked s node) * 8) \<le> 
    2 ^ LENGTH(32)"
  unfolding nodeValid_def Let_def
  apply (subgoal_tac "unat (ptr_val (next_C (h_val (hrs_mem (t_hrs_' s)) node))) < 2 ^ LENGTH(32)")
   apply (auto simp:if_split)[1] sorry(* 
  by (metis unat_lt2p word_bits_len_of) *)
    
lemma nodeValid_node_size_l1_new:
  "nodeValid s node \<Longrightarrow>  unat_ptr node + 8 + unat ((node_size_masked s node) * 8) \<le> 
    2 ^ LENGTH(32)" sorry
  
lemma nodeValid_node_size_l2:
  "nodeValid s node \<Longrightarrow>  
   unat_ptr (node +\<^sub>p 1) + unat (node_size_masked s node) * 8 \<le> 2 ^ LENGTH(32)"
  unfolding nodeValid_def Let_def    
  apply (subgoal_tac "unat_ptr (node_next s node) < 2 ^ LENGTH(32)")
   apply (subgoal_tac "unat (node_size_masked s node) * unat (8::word32) =
           unat ((node_size_masked s node) * 8)") 
    apply (auto simp:if_split)[1]
  sorry(* 
   apply (clarify)
   apply (subst (asm) eight_eq_eight[THEN sym])
   apply (frule unat_mult_lem[THEN iffD1]) 
   apply simp
  using unat_lt2p by blast  *)
lemma nodeValid_node_size_l2_new:
  "nodeValid s node \<Longrightarrow>  
   unat_ptr node + 8 + unat (node_size_masked s node) * 8 \<le> 2 ^ LENGTH(32)"
  sorry
    
lemma nodeValid_node_size_l3:
  "nodeValid s node \<Longrightarrow>
     8 + unat (node_size_masked s node) * 8 < 2 ^ LENGTH(32)"
  apply (subgoal_tac "ptr_val node > 0")
   apply (drule nodeValid_node_size_l2_new)
   apply unat_arith
  unfolding nodeValid_def Let_def apply clarify
  apply (drule c_guard_NULL) 
  apply (subgoal_tac "ptr_val node \<noteq> 0") 
  using word_neq_0_conv apply blast
  by (metis ptr.exhaust ptr_val.ptr_val_def)
    
function nodesValid :: "globals \<Rightarrow> mem_node_C ptr \<Rightarrow> bool" where
  "\<not> (nodeValid s heap) \<Longrightarrow> nodesValid s heap = False"
|"nodeValid s heap \<and> node_next s heap = NULL \<Longrightarrow> nodesValid s heap = True"
|"nodeValid s heap \<and> node_next s heap \<noteq> NULL \<Longrightarrow> nodesValid s heap =
      nodesValid s (node_next s heap)"
        apply auto by blast 
termination
  apply (relation "measure (\<lambda> (s,heap). 2 ^ 32 - unat_ptr heap)")
   apply auto
  unfolding nodeValid_def Let_def
  apply (clarsimp simp:ptr_less_simp ptr_le_simp)
  by unat_arith auto
    
    (* FIXME : remove if safe*)    
    (* declare nodesValid.simps[simp del]   *)
    
lemma nodesValid_def' :"nodesValid s heap =
  (let next = (node_next s heap) in 
    nodeValid s heap \<and> (next \<noteq> NULL \<longrightarrow> nodesValid s next))"
  unfolding Let_def
  using nodesValid.simps
  by blast
    
thm nodesValid.induct    
lemma nodesValid_induct' :
  "(\<And>s heap.
    (node_next s heap \<noteq> NULL \<Longrightarrow>
     P s (node_next s heap)) \<Longrightarrow>
    P s heap) \<Longrightarrow>
  P s node"    
  sorry
    
thm nodesValid.induct
thm nodesValid.simps
thm nodesValid_def'
  
definition heap_invs :: "globals \<Rightarrow> unit ptr \<Rightarrow> bool"
  where
    "heap_invs s heap \<equiv> nodesValid s (ptr_coerce heap)"
    
lemma nodesValid_nodeValid: "nodesValid s n \<Longrightarrow> nodeValid s n"
  apply(subst (asm) nodesValid_def') unfolding Let_def by auto
    
lemma nodesValid_not_null:
  "nodesValid s heap \<Longrightarrow> heap \<noteq> NULL"
  by (meson c_guard_NULL_simp nodeValid_def nodesValid_def') 
    
lemma heap_invs_not_null :"heap_invs s heap \<Longrightarrow> heap \<noteq> NULL" 
  unfolding heap_invs_def
  apply (drule nodesValid_not_null) by auto
    
lemma nodesValid_not_next_null:
  "nodesValid s node \<Longrightarrow> \<not> nodesValid s (node_next s node) \<Longrightarrow> (node_next s node) = NULL"
  using nodesValid.elims by auto 
    
lemma nodesValid_node_plus_1:
  "nodesValid s node \<Longrightarrow> node_next s node \<noteq> NULL \<Longrightarrow>
    (node +\<^sub>p 1) > node"
  sorry
    
function  reachable :: "globals \<Rightarrow> mem_node_C ptr \<Rightarrow> mem_node_C ptr \<Rightarrow> bool"
  where "reachable s NULL to = (to = NULL)"
  | "node \<noteq> NULL \<and> node = to \<Longrightarrow> reachable s node to = True"
  | "node \<noteq> NULL \<and> node \<noteq> to \<and> (node_next s node) \<noteq> NULL \<and>  (node_next s node) \<le>  node \<Longrightarrow>
    reachable s node to = False"
  | "node \<noteq> NULL \<and> node \<noteq> to \<and>  (node_next s node) >  node \<Longrightarrow>
     reachable s node to = (reachable s (node_next s node) to)"
  | "node \<noteq> NULL \<and> node \<noteq> to \<and> (node_next s node) = NULL  \<Longrightarrow>
     reachable s node to = (to = NULL)"
  by (auto simp: ptr_less_simp ptr_le_simp) fastforce
termination
  apply (relation "measure (\<lambda> (s,node,to).2 ^ 32 + unat_ptr to - unat_ptr node)")
   apply (auto simp: ptr_less_simp ptr_le_simp)
  by unat_arith auto
    
thm reachable.induct        
thm reachable.simps
  
  (* declare reachable.simps[simp del] *)
  
lemma self_reachable: "n \<noteq> NULL \<Longrightarrow> reachable s n n"
  by auto
    
lemma reachable_helper1[rule_format]: 
  "reachable s node to \<longrightarrow> node \<ge> (node_next s node) \<longrightarrow> to \<noteq> NULL \<longrightarrow> node = to"
  apply (rule_tac ?a0.0=s and ?a1.0=node and ?a2.0=to in reachable.induct)
      apply auto[3]
   apply (auto simp del:reachable.simps)
  by auto
    
lemma reachable_helper2[rule_format]: "reachable s node to \<longrightarrow> to \<noteq> NULL \<longrightarrow> node \<le> to"
  by (rule_tac ?a0.0=s and ?a1.0=node and ?a2.0=to in reachable.induct) auto
    
lemma reachable_helper3[rule_format]:
  "reachable s node to \<longrightarrow> node_next s node = NULL \<longrightarrow> node \<noteq> to \<longrightarrow> to = NULL "
  by (rule_tac ?a0.0=s and ?a1.0=node and ?a2.0=to in reachable.induct) auto  
    
lemma reachable_next_le_to[rule_format]:
  "reachable s node to \<longrightarrow> node \<noteq> to \<longrightarrow> to \<noteq> NULL \<longrightarrow> node_next s node \<le> to  "
  apply (rule_tac ?a0.0=s and ?a1.0=node and ?a2.0=to in reachable.induct)
      apply auto
  using reachable_helper2 by blast
    
    
lemma reachable_trans[rule_format]:
  "reachable s node to \<longrightarrow> to \<noteq> NULL \<longrightarrow> node_next s to > to \<longrightarrow> 
   reachable s node (node_next s to)"
  apply (rule_tac ?a0.0=s and ?a1.0=node and ?a2.0=to in  reachable.induct)
      apply auto
   apply (rule self_reachable) 
   apply (metis (full_types) ptr_less_def ptr_less_def' ptr_val.ptr_val_def word_not_simps(1))
  apply (simp add: ptr_less_simp)   
  apply (rule reachable.simps(4)[THEN iffD2])
   apply auto
   apply (drule_tac node="node_next s (node_next s to)" in reachable_helper2)
    apply simp
  by (auto simp: ptr_le_simp ptr_less_simp)  
    
lemma reachable_trans2[rule_format]:
  "reachable s node to \<longrightarrow> to \<noteq> NULL \<longrightarrow> node_next s to = NULL \<longrightarrow> 
   reachable s node (node_next s to)"
  apply (rule_tac ?a0.0=s and ?a1.0=node and ?a2.0=to in  reachable.induct)
  by auto
    
lemma updated_node_hrs_the_same_elsewhere_correct:
  assumes x_val:"x \<notin> ptr_span p"
  shows"hrs_the_same_at s (update_node s p new_node) x" 
  sorry
    
lemma updated_node_hrs_the_same_elsewhere_incorrect :
  assumes x_val:"x \<ge> ptr_val (p +\<^sub>p 1) \<or> x < ptr_val p"
  shows"hrs_the_same_at s (update_node s p new_node) x" 
proof-
  let ?xptr = "(Ptr x)::8 word ptr"
  have x[simp] : "ptr_val ?xptr = x" by simp
  hence "ptr_val ?xptr \<ge> ptr_val (p +\<^sub>p 1) \<or> ptr_val ?xptr < ptr_val p" sorry
  {assume "ptr_val ?xptr \<ge> ptr_val (p +\<^sub>p 1)"
    hence "ptr_span p \<inter> {ptr_val ?xptr..+size_of TYPE(8 word)} = {}" 
      unfolding intvl_def apply simp unfolding ptr_add_def apply simp  sorry
  }
  {assume "ptr_val ?xptr < ptr_val p"
    hence "ptr_span p \<inter> {ptr_val ?xptr..+size_of TYPE(8 word)} = {}" 
      unfolding intvl_def apply simp unfolding ptr_add_def   sorry
  }
  hence "ptr_span p \<inter> {ptr_val ?xptr..+size_of TYPE(8 word)} = {}" sorry (* oops *)
  hence "\<forall> h. h_val (heap_update p new_node h) ?xptr = h_val h ?xptr" 
    using h_val_update_regions_disjoint by blast
  hence "\<forall> h. (heap_update p new_node h)  x =  h x" 
    unfolding h_val_def
    apply (simp)
    by(simp add: from_bytes_eq)  
  thus "hrs_the_same_at s (update_node s p new_node) x"
    apply (simp add:t_hrs_'_t_hrs_'_update_simp)
    unfolding hrs_mem_update_def
    apply(simp split:prod.split)
    done
qed
thm t_hrs_'_update_def
thm t_hrs_'_def
  
lemma updated_node_blahblah:
  "x \<ge> ptr_val (p+\<^sub>p 1) \<and> x \<ge> ptr_val (q +\<^sub>p 1) \<Longrightarrow> 
    hrs_the_same_at s (update_node (update_node s p new_node_1) q new_node_2 ) x"
  (* FIXME error *)
  using updated_node_hrs_the_same_elsewhere
  by presburger
    
lemma updated_node_blahblah_2:
  "x < ptr_val p \<and> x < ptr_val q \<Longrightarrow> 
    hrs_the_same_at s (update_node (update_node s p new_node_1) q new_node_2 ) x"
  (* FIXME error *)
  using updated_node_hrs_the_same_elsewhere
  by presburger  
    
    
function path :: "globals \<Rightarrow> mem_node_C ptr \<Rightarrow> mem_node_C ptr \<Rightarrow> mem_node_C ptr list"
  where "node = NULL \<or> node \<ge> node_next s node \<or> node_next s node > to \<Longrightarrow>
          path s node to = []"
  |"node \<noteq> NULL \<and> 
    node < node_next s node \<and> 
    node_next s node \<le> to \<Longrightarrow>
    path s node to = node # (path s (node_next s node) to)"
     apply auto 
  by (metis  dual_order.strict_iff_order le_cases)
termination
  apply (relation "measure (\<lambda> (s,node,to).2 ^ 32 + unat_ptr to - unat_ptr node)")
   apply (auto simp:ptr_less_simp ptr_le_simp)
  by unat_arith     
    
lemma path_not_empty_node_cond[rule_format]: "set (path s node to) \<noteq> {} \<longrightarrow> 
        node \<noteq> NULL \<and>
        ptr_val node < ptr_val (node_next s node) \<and>
        ptr_val node < ptr_val to \<and> ptr_val (node_next s node) \<le> ptr_val to"
  apply (simp add:ptr_less_simp[THEN sym] ptr_le_simp[THEN sym] )
  apply (rule contrapos[THEN iffD2])
  apply (clarsimp)
  apply (rule path.simps)
  by auto
    
lemma p_in_path_not_in_next_eq : 
  assumes p_in_path: "p \<in> set (path s node to)" 
    and p_not_in_next: "p \<notin> set (path s (node_next s node) to)" 
  shows "p = node"
proof-
  from p_in_path have " (path s node to) = node # (path s (node_next s node) to)"
    by (metis emptyE empty_set path.elims)
  with p_in_path have "p \<in>  set (node # (path s (node_next s node) to))" by argo
  hence "p \<in> {node} \<union> set ((path s (node_next s node) to))" by (metis insert_is_Un list.simps(15)) 
  with p_not_in_next have " p \<in> {node}" by blast
  thus "p = node" by simp
qed
  
lemma p_in_path_l_to[rule_format]:  
  " p \<in> set (path s node to ) \<longrightarrow> p < to"
  apply (rule_tac ?P = "\<lambda> s node to. p \<in> set (path s node to ) \<longrightarrow> p < to" in path.induct)
  by auto
    
lemma p_in_path_ge_node[rule_format]:
  "p \<in> set (path s node to) \<longrightarrow> p \<ge> node"
  apply (rule_tac ?a0.0=s and ?a1.0=node and ?a2.0=to in path.induct)
  by auto
    
lemma p_in_path_next_le_to[rule_format]:
  "p \<in> set (path s node to) \<longrightarrow> (node_next s p) \<le> to"
  apply (rule_tac ?a0.0=s and ?a1.0=node and ?a2.0=to in path.induct)
  by auto
    
lemma p_in_path_l_next[rule_format]:
  "p \<in> set (path s node to) \<longrightarrow> node < (node_next s p)"
  apply (rule_tac ?a0.0=s and ?a1.0=node and ?a2.0=to in path.induct)
  by auto
    
lemma heaps_eq_imp_paths_eq:
  "\<forall> p . p \<ge> ptr_val fst_node \<and> p < ptr_val to \<longrightarrow> hrs_the_same_at  s s' p
       \<Longrightarrow>  path s fst_node to = path s' fst_node to" 
  apply (induction rule:path.induct)  
  sorry
    
lemma nodeValid_edge_of_addr_space:
  assumes "nodeValid s node"
  shows "(node +\<^sub>p 1) > node \<or> (node_size_masked s node) = 0"
  unfolding nodeValid_def
proof -
  have "unat (node_size_masked s node) * 8 < 2 ^ LENGTH(32)" using `nodeValid s node`
    unfolding nodeValid_def by meson
  hence "unat (node_size_masked s node) * 8 = unat ((node_size_masked s node) * 8)"
    using unat_mult_lem  by (metis sable_isa.eight_eq_eight)
  {assume "(node_size_masked s node) \<noteq> 0"    
    hence "(node_size_masked s node) * 8 \<noteq> 0"
      using `unat (node_size_masked s node) * 8 = unat ((node_size_masked s node) * 8)`
      using unat_eq_zero by fastforce
    hence "unat_ptr node + 8 < 2 ^ LENGTH(32)" 
      using `nodeValid s node` apply simp
      apply (frule nodeValid_node_size_l1_new) 
      apply auto
      by (meson add_le_same_cancel1 le_def less_le_trans not_gr_zero unat_eq_zero) 
    hence "(node +\<^sub>p 1) > node" 
      unfolding ptr_add_def 
      apply (simp add:ptr_less_simp)
      by unat_arith auto
  } thus ?thesis by fast
qed
  
lemma intvl_no_overflow_lower_bound:
  "(a :: ('a::{len}) word) \<in> {x ..+  sz} \<Longrightarrow> unat x + sz \<le> 2 ^ LENGTH('a) \<Longrightarrow> a \<ge> x"
  apply unat_arith unfolding intvl_def  apply unat_arith
  apply auto 
  apply (subgoal_tac "unat (of_nat k) = k")
   apply (smt add.commute add_leD1 add_less_mono1 order_less_le_trans unat_of_nat unat_of_nat_eq word_nchotomy)
  by (smt add.commute add.left_neutral add_diff_cancel_right' add_leD1 add_lessD1 diff_add_inverse diff_diff_cancel diff_le_self le_Suc_ex less_diff_conv less_irrefl_nat less_or_eq_imp_le linorder_not_less nat_add_left_cancel_less nat_less_le not_add_less1 order_less_le_trans unat_of_nat_eq)
    
lemma intvl_upper_bound: "a \<in> {x ..+ sz} \<Longrightarrow> 
  unat a < unat x + sz"
  unfolding intvl_def
  apply unat_arith
  apply (auto simp add: unat_of_nat) 
  using mod_less by blast
    
    (* thm zero_not_in_intvl_no_overflow[THEN intvl_no_overflow_lower_bound] *)
lemma zero_not_in_intvl_lower_bound:
  "(a::('a::len) word) \<in> {x ..+ sz} \<Longrightarrow> 0 \<notin> {x ..+  sz}  \<Longrightarrow> a \<ge>  x "
  apply (drule zero_not_in_intvl_no_overflow)
  by (rule intvl_no_overflow_lower_bound)
    
lemma hrs_the_same_imp_nodeValid:
  "\<forall> p \<in> ptr_span node. hrs_the_same_at s s' p \<Longrightarrow>
   \<forall> p \<in> array_span (node +\<^sub>p 1) (unat (node_size_masked s node)). hrs_the_same_at s s' p \<Longrightarrow>   
   nodeValid s node \<Longrightarrow> 
   nodeValid s' node"
  unfolding nodeValid_def nodeFree_def Let_def
  apply (subgoal_tac "node_next s node = node_next s' node")
   apply (subgoal_tac "node_size s node = node_size s' node")
    apply(frule hrs_the_same_nodes_the_same)
    apply clarsimp
    apply (simp add:hrs_htd_def )
    apply auto[1]
   apply (frule hrs_the_same_nodes_the_same) apply auto[1]
  apply (frule hrs_the_same_nodes_the_same) apply auto[1]
  done
    
lemma hrs_the_same_imp_nodeValid2:
  assumes hrs_the_same:"\<forall> p . p\<ge> ptr_val node \<and> unat p < unat_ptr node + 8 + (unat (node_size_masked s node)) * 8 \<longrightarrow>
    hrs_the_same_at s s' p"
    and "nodeValid s node"
  shows "nodeValid s' node"
proof-
  have 1:"\<forall> p \<in> ptr_span node. p \<ge> ptr_val node" using `nodeValid s node`
    apply auto
    unfolding nodeValid_def c_guard_def c_null_guard_def
    apply (rule intvl_no_overflow_lower_bound)
     apply auto[1] 
    by (metis mem_node_C_size zero_not_in_intvl_no_overflow)     
  have "\<forall> p \<in> ptr_span node. unat p <unat_ptr node + 8" 
    using sable_isa.intvl_upper_bound by auto
  hence "\<forall> p \<in> ptr_span node. unat p <unat_ptr node + 8 + (unat (node_size_masked s node)) * 8"
    by auto
  with 1 have c1:"\<forall> p \<in> ptr_span node. hrs_the_same_at s s' p" 
    using hrs_the_same by simp
      
  let ?arr_span = "array_span (node +\<^sub>p 1) (unat (node_size_masked s node))"  
  have "(node +\<^sub>p 1) > node \<or> (node_size_masked s node) = 0"
    using `nodeValid s node` nodeValid_edge_of_addr_space by simp
  moreover {
    assume "(node +\<^sub>p 1) > node"  
    have "\<forall>p \<in> ?arr_span . p \<ge> ptr_val node"
      apply auto
      apply (frule intvl_no_overflow_lower_bound)
      using `nodeValid s node`
      using sable_isa.nodeValid_node_size_l2 apply blast
      using `(node +\<^sub>p 1) > node`
      by (meson le_less_trans less_irrefl nat_le_linear ptr_less_def ptr_less_def' word_le_nat_alt)
    moreover have "\<forall>p \<in> ?arr_span.unat p < unat_ptr node + 8 + (unat (node_size_masked s node)) * 8"
      apply auto
      apply (drule intvl_upper_bound) 
      unfolding ptr_add_def
      by unat_arith
    ultimately have "\<forall>p \<in> ?arr_span. hrs_the_same_at s s' p" 
      using hrs_the_same by simp
  }
  moreover{
    assume "(node_size_masked s node) = 0"
    hence "?arr_span = {}" by simp
    hence "\<forall> p \<in> ?arr_span. hrs_the_same_at s s' p" by blast
  }
  ultimately have "\<forall> p \<in> ?arr_span. hrs_the_same_at s s' p" by argo
  with `nodeValid s node` c1 show ?thesis
    using hrs_the_same_imp_nodeValid by presburger
qed
  
lemma nodeValid_imp_range_l:
  "ptr_val n < ptr_val to \<Longrightarrow> nodeValid s n \<Longrightarrow> nodeValid s to \<Longrightarrow> 
      \<forall> p \<in> ptr_span n. p < ptr_val to"
  sorry
    
lemma nodesValid_trans_back: "nodeValid s node \<Longrightarrow> 
    nodesValid s (node_next s node) \<Longrightarrow>
    nodesValid s node"
  by(subst nodesValid_def', simp)
    
thm nodesValid.induct[simplified]
lemma nodesValid_reachable_imp_nodesValid: 
  "reachable s fst_node node \<Longrightarrow>
   nodesValid s fst_node \<Longrightarrow>  
   node \<noteq> NULL \<Longrightarrow> 
   nodesValid s node"
proof (induction fst_node rule:nodesValid_induct')
  fix s heap
  assume ih: "( next_C (h_val (hrs_mem (t_hrs_' s)) heap) \<noteq> NULL \<Longrightarrow>            
             reachable s (next_C (h_val (hrs_mem (t_hrs_' s)) heap)) node \<Longrightarrow>
             nodesValid s (next_C (h_val (hrs_mem (t_hrs_' s)) heap)) \<Longrightarrow>
             node \<noteq> NULL \<Longrightarrow> nodesValid s node)"
    and "nodesValid s heap"
    and "reachable s heap node"
    and "node \<noteq> NULL"
  let ?heap_next = "node_next s heap"
  {
    assume "node = heap"
    hence "nodesValid s node" using `nodesValid s heap` by auto
  }
  moreover {
    assume "node \<noteq> heap"
    {assume "?heap_next = NULL"
      hence "node = NULL" using `node \<noteq> heap` `nodesValid s heap` `reachable s heap node` 
        using sable_isa.reachable_helper3 by blast 
      with `node \<noteq> NULL` have False by auto
    } hence "?heap_next \<noteq> NULL" by auto
    moreover from `nodesValid s heap` `?heap_next \<noteq> NULL` have "nodesValid s ?heap_next" 
      by (meson sable_isa.nodesValid_def')  
    moreover from `reachable s heap node` `node \<noteq> NULL` `?heap_next \<noteq> NULL` `node \<noteq> heap`
    have "reachable s ?heap_next node"  
      using reachable.elims(2) by blast
    ultimately have "nodesValid s node"
      using `node \<noteq> NULL` ih  by blast   
  }
  ultimately show "nodesValid s node" by auto 
qed
  
lemma nodesValid_reachable_imp_next_reachable: 
  "reachable s fst_node node \<Longrightarrow>
   nodesValid s fst_node \<Longrightarrow>    
   node \<noteq> NULL \<Longrightarrow> 
   reachable s fst_node (node_next s node)"
  apply (frule nodesValid_reachable_imp_nodesValid) 
    apply assumption+
proof-
  fix s fst_node node
  assume "nodesValid s fst_node" 
    and reachable: "reachable s fst_node node"
    and  "node \<noteq> NULL" 
    and  "nodesValid s node"    
  have "nodeValid s node" using `nodesValid s node` nodesValid_def' by metis
  {assume "node_next s node \<noteq> NULL"
    hence "node_next s node > node" using `nodeValid s node` unfolding nodeValid_def
      by meson
    hence "reachable s fst_node (node_next s node)" 
      using reachable `node \<noteq> NULL` reachable_trans
      by presburger
  } moreover{ assume "node_next s node = NULL"
    hence "reachable s fst_node (node_next s node)" using reachable `node \<noteq> NULL` 
        reachable_trans2 by presburger
  }
  ultimately show "reachable s fst_node (node_next s node)" by argo
qed      
  
lemma nodesValid_reachable_imp_nodeValid: "nodesValid s heap \<Longrightarrow> reachable s  heap node
      \<Longrightarrow> node \<noteq> NULL \<Longrightarrow> nodeValid s node"
  apply (drule nodesValid_reachable_imp_nodesValid)
  by assumption+ (meson nodesValid_def')
    
thm word_mult_le_mono1
  
lemma l10: "unat x + unat y < 2 ^ 32 \<Longrightarrow>y \<noteq> 0 \<Longrightarrow> 
            ((x:: word32) div ( y :: word32)) * y + y \<ge> x"
  apply (subgoal_tac "unat (x div y * y) = (unat x div unat y) * unat y")
    
  sorry
    
lemma l11:"((x::word32) || (scast (y::  32 signed word))) && (scast (~~y)) = x && (scast (~~y))"
  apply (subst word_ao_dist)
proof -
  have " ((scast y)::word32) && scast (~~ y) = 0" unfolding scast_def sorry
  hence " x && scast (~~ y) || scast y && scast (~~ y) = x && scast (~~ y) || 0"
    by (simp add: \<open>scast y && scast (~~ y) = 0\<close>)
  thus "x && scast (~~ y) || scast y && scast (~~ y) = x && scast (~~ y)"  by simp
qed
  
lemma mask_sw32_eq_0_eq_x :
  assumes "(x::word32) && scast (flag:: 32 signed word) = 0"
  shows " x && scast (~~flag) = x"
proof -
  let ?flag_w32 = "(scast flag)::word32"
  let ?neg_flag_w32 =  "scast (~~flag) :: word32"
  have l1[simp]: "?neg_flag_w32 = ~~ ?flag_w32" sorry
  thus ?thesis using assms by (simp add: mask_eq_0_eq_x)
qed
  
  (* declare [[show_types]]  *)
  (* declare [[show_sorts]] *)
  (* declare [[show_consts]] *)
  
lemma hrs_the_sam_nodesValid_reachable_imp_reachable:
  assumes "reachable s heap node"
    and "nodesValid s heap"
    and "\<forall>p . p \<ge> ptr_val heap \<and> p < ptr_val node \<longrightarrow> hrs_the_same_at s s' p"
    and "node \<noteq> NULL"
  shows "reachable s' heap node" 
  sorry
    
lemma node_in_path_nodesValid_imp_nodeValid_node[rule_format]:
  "n \<in> set (path s fst_node to) \<longrightarrow> 
   nodesValid s fst_node \<longrightarrow>
   nodeValid s n" 
  apply (rule_tac ?a0.0=s and ?a1.0=fst_node and ?a2.0= to in path.induct)
   apply auto 
    apply (erule nodesValid_nodeValid)+
  apply (frule nodesValid_not_next_null)
  by auto
    
lemma nodesValid_reachable_imp_in_path: 
  assumes nodesValid: "nodesValid s fst_node" 
    and reachable:"reachable s fst_node to"
    and "to \<noteq> NULL" and "fst_node \<noteq> to"
  shows  "fst_node \<in> set (path s fst_node to)"
proof-
  let ?next = "node_next s fst_node"
  from nodesValid have "nodeValid s fst_node" using nodesValid_def' by meson
  hence "c_guard fst_node" and  "?next \<noteq> NULL \<longrightarrow> ?next > fst_node" unfolding nodeValid_def
    by meson+
  moreover from reachable and `fst_node \<noteq> to` `to \<noteq> NULL` 
  have "?next \<noteq> NULL" using reachable_helper3 by blast 
  ultimately have "?next > fst_node" by simp
  have "fst_node \<noteq> NULL" using `c_guard fst_node` by force
  have "reachable s ?next to" 
    using `fst_node < ?next` `fst_node \<noteq> NULL` `fst_node \<noteq> to` reachable
      reachable.simps(4) by simp
  hence "?next \<le> to" using `to \<noteq> NULL` by (rule reachable_helper2) 
  hence "path s fst_node to = fst_node # path s ?next to" 
    using `fst_node \<noteq> NULL` `fst_node < ?next` `?next \<le> to`    
      path.simps(2) by fast
  thus ?thesis by simp
qed
  
lemma node_reachable_in_path[rule_format]:
  "reachable s node to \<longrightarrow> node \<noteq> to\<longrightarrow> to \<noteq> NULL \<longrightarrow> node \<in> set (path s node to )"
  apply(rule_tac ?a0.0=s and ?a1.0=node and ?a2.0=to in reachable.induct)
      apply auto
  apply(subgoal_tac "set (path s (node_next s node) to) \<noteq> {}")
   apply (frule path_not_empty_node_cond)
   apply (subgoal_tac "(node_next s node) \<le> to")
  by (auto simp:ptr_le_simp ptr_less_simp)
    
lemma nodeValid_heaps_eq_imp_nodeValid:
  assumes "nodeValid s node"
    and heaps_eq:"\<forall>x. x \<ge> ptr_val node \<longrightarrow> hrs_the_same_at s s' x"
  shows " nodeValid s' node"
proof-
  let ?node_size = "(node_size_masked s node)"
  have "c_guard node" using `nodeValid s node` unfolding nodeValid_def by meson
  have "unat ?node_size * 8 < 2 ^ LENGTH(32)" using `nodeValid s node`
    unfolding nodeValid_def by meson
  hence "unat ?node_size * 8 = unat (?node_size * 8)"
    using unat_mult_lem  by (metis sable_isa.eight_eq_eight)
  have 0:"unat_ptr (node +\<^sub>p 1) + unat (?node_size * 8) \<le>  2 ^ LENGTH(32)"
    using `nodeValid s node` by (rule nodeValid_node_size_l1)      
  have "\<forall> p \<in> ptr_span node. p \<ge> ptr_val node" 
    using `c_guard node` unfolding c_guard_def c_null_guard_def
    apply auto
    apply (drule zero_not_in_intvl_no_overflow)
    apply (erule intvl_no_overflow_lower_bound) by assumption
  hence 1:"\<forall> p \<in> ptr_span node. hrs_the_same_at s s' p" using heaps_eq
    by blast
  have 2:"\<forall> p \<in> array_span (node +\<^sub>p 1) (unat ?node_size). p \<ge> ptr_val (node +\<^sub>p 1)"
    using 0
      `unat ?node_size * 8 = unat (?node_size * 8)`
    unfolding intvl_def
    apply unat_arith
    apply auto 
    by (simp add: nat_less_le order_less_le_trans unat_of_nat_eq)
  {
    assume "(node +\<^sub>p 1) > node"
    hence "\<forall>p \<in> array_span (node +\<^sub>p 1) (unat ?node_size). hrs_the_same_at s s' p"   
      using 2 heaps_eq 
      by (meson dual_order.strict_iff_order less_le_trans ptr_less_def ptr_less_def')
  }moreover {
    assume "\<not>(node +\<^sub>p 1) > node"
    hence "?node_size = 0" 
      using `nodeValid s node` nodeValid_edge_of_addr_space by blast
    hence "array_span (node +\<^sub>p 1) (unat ?node_size) = {}"
      by simp
    hence "\<forall>p \<in> array_span (node +\<^sub>p 1) (unat ?node_size). hrs_the_same_at s s' p"   
      by blast
  }
  ultimately have 3:"\<forall>p \<in> array_span (node +\<^sub>p 1) (unat ?node_size). hrs_the_same_at s s' p"
    by blast
  show ?thesis using `nodeValid s node` 1 3 hrs_the_same_imp_nodeValid by blast
qed
  
lemma nodesValid_heaps_eq_imp_nodesValid[rule_format]:
  "nodesValid s node \<longrightarrow> 
   (\<forall>x. x \<ge> ptr_val node \<longrightarrow> hrs_the_same_at s s' x) \<longrightarrow>
   nodesValid s' node"
  apply (rule_tac ?a0.0=s and ?a1.0=node in nodesValid.induct)
    apply auto[1]
   defer
   apply clarify
   defer
proof clarify
  fix s heap
  assume "nodeValid s heap"
    "node_next s heap = NULL"
    "nodesValid s heap"
    and hrs_the_same:"\<forall>x\<ge>ptr_val heap. hrs_the_same_at s s' x"  
  have "c_guard heap" using `nodeValid s heap` unfolding nodeValid_def by meson
  hence "\<forall> p \<in> ptr_span heap. p \<ge> ptr_val heap" 
    unfolding c_guard_def c_null_guard_def
    apply auto
    apply (drule zero_not_in_intvl_no_overflow)
    apply (erule intvl_no_overflow_lower_bound) by assumption
  hence "\<forall> p \<in> ptr_span heap. hrs_the_same_at s s' p" using hrs_the_same by blast
  hence "node_val s heap = node_val s' heap" using hrs_the_same_nodes_the_same by blast     
  hence "node_next s' heap = NULL" using `node_next s heap = NULL` by argo
      
  have "nodeValid s' heap" using `nodeValid s heap` hrs_the_same 
    using nodeValid_heaps_eq_imp_nodeValid by blast
  show "nodesValid s' heap" using `node_next s' heap = NULL` `nodeValid s' heap`
    by auto
next 
  fix s heap
  assume ih: "nodesValid s (node_next s heap) \<longrightarrow>
          (\<forall>x\<ge>ptr_val (node_next s heap).hrs_the_same_at s s' x) \<longrightarrow>
          nodesValid s' (node_next s heap)"
    and "nodeValid s heap"
    and "node_next s heap \<noteq> NULL"
    and "nodesValid s heap"
    and hrs_the_same:"\<forall>x\<ge>ptr_val heap. hrs_the_same_at s s' x"
  have "c_guard heap" using `nodeValid s heap` unfolding nodeValid_def by meson
  have "\<forall>p \<in> ptr_span heap. hrs_the_same_at s s' p" using `c_guard heap` hrs_the_same
    unfolding c_guard_def c_null_guard_def
    unfolding intvl_def apply simp
    by (meson le_def less_le_trans word_wrap_of_natD) 
  hence "node_val s heap = node_val s' heap" using hrs_the_same_nodes_the_same by blast
  have "node_next s heap > heap" using `nodeValid s heap` `node_next s heap \<noteq> NULL`
    unfolding nodeValid_def by meson
  have "nodesValid s (node_next s heap)"
    using `node_next s heap \<noteq> NULL` `nodesValid s heap` 
    using nodesValid.simps by blast
  moreover have "(\<forall>x\<ge>ptr_val (node_next s heap).hrs_the_same_at s s' x)"
    using hrs_the_same `node_next s heap > heap`
    by (simp add: ptr_less_simp) 
  ultimately have "nodesValid s' (node_next s heap)" using ih by blast
  hence "nodesValid s' (node_next s' heap)" 
    using `node_val s heap = node_val s' heap` by argo      
  moreover have "nodeValid s' heap" using hrs_the_same `nodeValid s heap` 
    using nodeValid_heaps_eq_imp_nodeValid by blast
  ultimately show "nodesValid s' heap" using nodesValid_trans_back by fast
qed 
  
thm nodesValid_reachable_imp_in_path
lemma path_nodeValid_reachable_imp_nodesValid[rule_format]:
  "nodeValid s heap \<longrightarrow>
       (\<forall> p \<in> set (path s heap node). nodeValid s p) \<longrightarrow>
       reachable s heap node \<longrightarrow>
       nodesValid s node \<longrightarrow>
       nodesValid s heap"
  apply (rule_tac ?a0.0=s and ?a1.0=heap and ?a2.0=node in path.induct) 
   apply (unfold nodeValid_def)[1] unfolding Let_def
   apply clarify
   apply (drule c_guard_NULL)
   apply auto[1]
        apply (metis sable_isa.nodesValid_not_null sable_isa.reachable_helper1)
       apply (metis reachable_helper1 sable_isa.nodesValid_not_null)
  using reachable_helper3 apply blast
     apply (metis dual_order.strict_iff_order order_less_le_trans sable_isa.nodesValid_not_null sable_isa.reachable.simps(4) sable_isa.reachable_helper2)
  using reachable_helper3 apply blast
   apply (metis dual_order.strict_iff_order order_less_le_trans reachable_helper2 sable_isa.nodesValid_not_null sable_isa.reachable.simps(4))   
  apply auto
   apply (frule node_reachable_in_path)
     apply auto
   apply (frule nodesValid_not_null, auto)
  using sable_isa.nodesValid_def' unfolding Let_def by blast
    
lemma nodesValid_l3:
  "nodeValid s node \<Longrightarrow>
   node_next s node = NULL \<Longrightarrow>
    nodesValid s node"
  by (meson nodesValid_def')
    
lemma c_guard_l1:
  assumes "c_guard (a::('a::mem_type) ptr)"
    "\<not> c_guard (a +\<^sub>p 1)"
    "b > a" 
    "b \<ge> a +\<^sub>p 1"
  shows "\<not> c_null_guard b" 
proof -
  have "\<not> c_null_guard ( a +\<^sub>p 1)" using `c_guard a` `\<not> c_guard (a +\<^sub>p 1)`
    unfolding c_guard_def apply auto    
    apply(frule ptr_aligned_plus[where i = 1]) by auto
  hence "0 \<in> ptr_span (a +\<^sub>p 1)" unfolding c_null_guard_def by auto
  have "0 \<in> ptr_span b" using `b \<ge> a +\<^sub>p 1` using `0 \<in> ptr_span (a +\<^sub>p 1)` unfolding intvl_def
  proof simp
    assume "a +\<^sub>p 1 \<le> b"
      and "\<exists>k. ptr_val (a +\<^sub>p 1) + of_nat k = 0 \<and> k < size_of TYPE('a)"
    then obtain k where k:"ptr_val (a +\<^sub>p 1) + of_nat k = 0 \<and> k < size_of TYPE('a)" by auto
    hence "ptr_val (a +\<^sub>p 1) + of_nat k = 0" by auto
    {
      assume "((of_nat k)::32 word) \<noteq> 0"
      have "ptr_val b \<ge> ptr_val (a +\<^sub>p 1)" using `b \<ge> a +\<^sub>p 1`  by (simp add: ptr_le_def ptr_le_def')
      hence 1:"ptr_val b - ptr_val (a +\<^sub>p 1) \<le> of_nat k" 
        using `ptr_val (a +\<^sub>p 1) + of_nat k = 0`
        apply unat_arith apply auto
        using `of_nat k \<noteq> 0` 
        apply (subgoal_tac "unat ((of_nat k)::32 word) = 0 \<Longrightarrow> ((of_nat k)::32 word) = 0")
         apply auto[1]
        apply (subst (asm) (3) unat_eq_0)  by auto
          
      let ?k2' = "of_nat k - ( ptr_val b - ptr_val (a +\<^sub>p 1))"
      have "ptr_val b + ?k2' = of_nat k + ptr_val (a +\<^sub>p 1)" by simp
      hence "ptr_val b + ?k2' = 0" using k by (simp add: add.commute)
      hence 2:"ptr_val b + of_nat (unat ?k2') = 0" by simp
          
      let ?of_nat_k = "((of_nat k):: 32 word)"
      have "?k2' \<le> ?of_nat_k" using 1  word_sub_le by auto
      hence "unat ?k2' \<le> unat ?of_nat_k" by (simp add: word_le_nat_alt) 
      moreover have "unat ?of_nat_k \<le> k" by (metis le_cases le_unat_uoi) 
      moreover  have "k < size_of TYPE('a)" using k by simp
      ultimately have "(unat ?k2') < size_of TYPE('a)" by simp
      hence "ptr_val b + of_nat (unat ?k2') = 0 \<and> (unat ?k2') < size_of TYPE('a)" using 2 by simp
      hence "\<exists>k::nat. ptr_val b + of_nat k = (0::32 word) \<and> k < size_of TYPE('a)" by (frule exI)
    }
    moreover{  
      assume k_eq_0:"((of_nat k)::32 word) = 0" 
      let ?k2' = "of_nat (size_of TYPE('a)) - ( ptr_val b - ptr_val a)"
      have "ptr_val b > ptr_val a" using `b>a` 
        by (simp add: ptr_less_def ptr_less_def')
      hence "unat_ptr b > unat_ptr a" using unat_mono by auto
      from k_eq_0 have "ptr_val (a +\<^sub>p 1)= 0" using k by unat_arith
      hence 1:"ptr_val a + of_nat (size_of TYPE('a)) = 0" unfolding ptr_add_def by simp
      hence 2: "ptr_val b - ptr_val a < of_nat (size_of TYPE('a))" 
        using k_eq_0
        apply unat_arith (* SLOW! *) apply auto
         apply (subgoal_tac "unat_ptr a \<noteq> (0::nat)")
          apply auto[1]
        using `c_guard a` 
         apply (metis len_of_addr_card max_size mem_type_simps(3) neq0_conv unat_of_nat_len)
        using `unat_ptr b > unat_ptr a` by simp
      hence "ptr_val b + ?k2' = 0" using 1  by (simp add: add.commute)
      hence 3:"ptr_val b + of_nat (unat ?k2') = 0" by simp
      have "ptr_val b - ptr_val a > 0" using `ptr_val b > ptr_val a` 
        using word_neq_0_conv by fastforce 
      with 2 have "?k2' < of_nat (size_of TYPE('a))"  by unat_arith (* VERY SLOW! *)
      hence "unat ?k2' < size_of TYPE('a)" using unat_less_helper by auto
      with 3 have "ptr_val b + of_nat (unat ?k2') = 0 \<and> unat ?k2' < size_of TYPE('a)" by auto
      hence "\<exists>k::nat. ptr_val b + of_nat k = (0::32 word) \<and> k < size_of TYPE('a)" by (frule exI)  
    }
    ultimately show "\<exists>k::nat. ptr_val b + of_nat k = (0::32 word) \<and> k < size_of TYPE('a)"
      by auto
  qed 
  thus "\<not> c_null_guard b" unfolding c_null_guard_def by auto
qed
  
lemma self_impl: "Q \<Longrightarrow> Q" by assumption
    
lemma nodeValid_next_val: "nodeValid s node \<Longrightarrow>
  node_next s node \<noteq> NULL \<Longrightarrow>
  unat_ptr (node_next s node) \<ge> unat_ptr node + 8 +  unat ((node_size_masked s node) * 8)"
  unfolding nodeValid_def Let_def 
  by(simp split:if_split) 
    
    (* FIXME put somewhere else *)    
lemma unat_add_lem_3:
  "unat (a::'a::len word) + unat b + unat c < 2 ^ LENGTH('a) =
    (unat (a + b + c) = unat a + unat b + unat c)"
  using unat_add_lem
  by (metis add_lessD1 unat_lt2p) 
    
    (* consider adding more to the conclusion *)
lemma nodesValid_heaps_eq_nodeValid_in_path: 
  assumes "nodesValid s heap"
    and hrs_the_same: "\<forall> p . p \<ge> ptr_val heap \<and> p < ptr_val to \<longrightarrow> hrs_the_same_at s s' p"
    and "reachable s heap to"
    and "to \<noteq> NULL"
  shows "\<forall> n \<in> set (path s' heap to). nodeValid s' n"
proof-  
  have "path s heap to = path s' heap to" using hrs_the_same 
    using heaps_eq_imp_paths_eq by blast
  { fix n
    assume n_in_path_s':"n \<in> set (path s' heap to)"    
    hence n_in_path:"n \<in> set (path s heap to)" using `path s heap to = path s' heap to`
      by argo
    have "n \<ge> heap" using n_in_path 
      using p_in_path_ge_node by blast
    have "nodeValid s n" using n_in_path `nodesValid s heap` 
      using node_in_path_nodesValid_imp_nodeValid_node by blast
    have c1:"\<forall> p . p\<ge> ptr_val n \<longrightarrow> p \<ge> ptr_val heap" using `n \<ge> heap` 
      apply(simp add: ptr_le_simp) 
      by fastforce
    have "node_next s n \<noteq> NULL" using n_in_path
      apply auto
      apply(drule p_in_path_l_next) 
      by (simp add: ptr_less_def ptr_less_def')
    hence "unat_ptr n + 8 + unat ((node_size_masked s n) * 8) \<le> unat_ptr (node_next s n)"
      using `nodeValid s n` sable_isa.nodeValid_next_val by blast
    moreover have "node_next s n \<le> to" using n_in_path 
      using p_in_path_next_le_to by fast
    ultimately have "unat_ptr n + 8 + unat ((node_size_masked s n) * 8) \<le> unat_ptr to"
      apply(auto simp:ptr_le_simp) by unat_arith 
    hence "unat_ptr n + 8 + unat (node_size_masked s n) * 8 \<le> unat_ptr to"     
      apply unat_arith apply auto 
      by (metis \<open>nodeValid s n\<close> nodeValid_def sable_isa.eight_eq_eight unat_of_nat_eq word_arith_nat_mult)
    hence c2:"\<forall> p . unat p < unat_ptr n + 8 + (unat (node_size_masked s n)) * 8
      \<longrightarrow> p <ptr_val to" apply auto 
      using less_le_trans word_less_nat_alt by blast     
    have "\<forall> p . p\<ge> ptr_val n \<and> unat p < unat_ptr n + 8 + (unat (node_size_masked s n)) * 8 \<longrightarrow>
      hrs_the_same_at s s' p" using c1 c2
      using hrs_the_same by presburger
    with `nodeValid s n` have "nodeValid s' n" 
      using hrs_the_same_imp_nodeValid2 by presburger
  }
  thus ?thesis by fast
qed
  
  (*FIXME move these out of here  *) 
  
lemma OCC_FLAG_helper1: "(x::32 word) && (scast OCC_FLG) = 0 \<Longrightarrow>
    y \<le> x \<Longrightarrow>
    y && (scast OCC_FLG) = 0"
  apply(subgoal_tac "scast OCC_FLG = ~~ ((mask 31)::32 word)")
   apply(subgoal_tac "y && mask 31 = y ")
    apply (frule mask_eq_x_eq_0[THEN iffD1])
    apply simp
   apply (subgoal_tac "x \<le> mask 31")
    apply (metis (no_types, hide_lams) and_mask_eq_iff_le_mask less_le_trans not_less)
   apply (metis add.left_neutral word_and_le1 word_bool_alg.double_compl word_plus_and_or_coroll2)
  unfolding MEM_NODE_OCCUPIED_FLAG_def mask_def
  by simp
    
lemma OCC_FLG_neg : "(scast (~~ MEM_NODE_OCCUPIED_FLAG) ::32 word) = ~~ scast MEM_NODE_OCCUPIED_FLAG"
  by (metis (no_types) mask_eq_0_eq_x l11 mask_sw32_eq_0_eq_x word_bw_comms(1) word_log_esimps(7) 
      word_log_esimps(9) word_not_not)
    
lemma unat_addition_less_pres:"unat (a::'a::len word) + unat b < unat c \<Longrightarrow> a + b < c"
  by unat_arith
lemma unat_addition_le_pres:"unat (a::'a::len word) + unat b \<le> unat c \<Longrightarrow> a + b \<le> c"
  by unat_arith
lemma shiftr3_upper_bound:"(x :: 32 word) >> 3 \<le> 0x1FFFFFFF"
  apply (simp add:shiftr3_is_div_8)
  apply unat_arith
  by auto
thm intvl_no_overflow   
lemma intvl_no_overflow2:
  "unat (a::'a::len word) + b \<le> 2 ^ LENGTH('a) \<Longrightarrow>
(x \<in> {a..+b}) = (a \<le> x \<and> unat x < unat a + b)"
  sorry
thm intvl_no_overflow2[THEN iffD1]
  
lemma alloc'_invs:
  fixes size_bytes:: "32 word" and heap:: "unit ptr"
  assumes size_bytes_g0 : "size_bytes > 0"
  shows "\<lbrace>\<lambda>s. heap_invs s heap \<rbrace> (alloc' heap size_bytes) \<lbrace> \<lambda>r s. heap_invs s heap \<rbrace>"
  unfolding alloc'_def Let_def 
  apply (simp add: h_val_field_from_bytes)
  apply (subst whileLoop_add_inv 
      [where I="\<lambda> (n,r) s. heap_invs s heap \<and> reachable s (ptr_coerce heap) n
                  \<and> (r=0 \<longrightarrow> (n = NULL \<or> ((size_bytes >> 3) + 1
                        \<le> size_C (h_val (hrs_mem (t_hrs_' s)) n) && scast (~~ OCC_FLG))
                     \<and> size_C (h_val (hrs_mem (t_hrs_' s)) n) && scast OCC_FLG = 0))" 
        and M="\<lambda> ((n,y),s). ptr_val n"])
  apply (wp )
      prefer 5
      apply (rule_tac Q="heap_invs s heap" in self_impl, simp)
     prefer 4
     apply (simp add: size_bytes_g0)
     apply (rule return_wp) 
  unfolding heap_invs_def
  using [[simp_trace=false]] using [[simp_trace_depth_limit=1000]]
    apply (auto)
                    apply(drule c_guard_NULL, drule nodesValid_reachable_imp_next_reachable, auto)+  
                 apply (drule one_mask_neg_MNOF_not_zero, solves simp)
                apply(drule c_guard_NULL, drule nodesValid_reachable_imp_next_reachable, auto)+
              apply (drule mask_sw32_eq_0_eq_x, solves simp)
             apply(drule c_guard_NULL, frule nodesValid_reachable_imp_next_reachable, auto)+
         apply (drule one_mask_neg_MNOF_not_zero, solves simp)
        apply(drule c_guard_NULL, drule nodesValid_reachable_imp_next_reachable, auto)+
      apply (frule mask_sw32_eq_0_eq_x, solves simp)
     apply(drule c_guard_NULL, drule nodesValid_reachable_imp_next_reachable, auto)    
    prefer 3
    apply (wp, auto)
     apply (drule nodesValid_not_null, simp)
     apply (drule one_mask_neg_MNOF_not_zero, auto)
    apply (drule nodesValid_not_null, simp)
    apply (frule mask_sw32_eq_0_eq_x, solves simp)
   apply (frule nodesValid_not_null, simp)
proof -
  fix a::"mem_node_C ptr"
  fix s::globals
  assume invs: "nodesValid s (ptr_coerce heap)"
    and node_free :"node_size s a && scast OCC_FLG = 0"
    and reachable: "reachable s (ptr_coerce heap) a"
    and "a \<noteq> NULL"
    and "c_guard a"
    (* and "c_guard (a +\<^sub>p uint (2 + (size_bytes >> 3))) " *)
  let ?new_size_simplified = "(node_size s a && scast (~~ OCC_FLG) ||  scast OCC_FLG)"
  let ?new_s = "(update_node s a (mem_node_C
                (node_size s a && scast (~~ OCC_FLG) ||  scast OCC_FLG)
                (node_next s a)))"
  let ?new_size = "(node_size ?new_s a)"
  let ?heap_node = "(ptr_coerce heap) :: mem_node_C ptr"
  have "nodeValid s ?heap_node"  using `nodesValid s ?heap_node` 
    using nodesValid_nodeValid by blast
  hence "c_guard ?heap_node" unfolding nodeValid_def by metis
  from invs and reachable and `a \<noteq> NULL` have "nodesValid s a"
    using nodesValid_reachable_imp_nodesValid by simp
  have "node_next ?new_s a = node_next s a" using updated_node_next by auto
  have "?new_size = ?new_size_simplified" using updated_node_size by auto
  have "?new_size_simplified  && scast (~~OCC_FLG) =
    node_size s a && scast (~~ OCC_FLG) && scast (~~OCC_FLG)"
    using l11 by (simp add: word_bw_assocs(1))
  hence size_masked_the_eq:"node_size s a && scast (~~ OCC_FLG) =
        ?new_size  && scast (~~OCC_FLG)"
    apply (subst `?new_size = ?new_size_simplified`) by simp
  moreover have new_node_occupied: "?new_size_simplified && scast OCC_FLG = scast OCC_FLG"
    unfolding MEM_NODE_OCCUPIED_FLAG_def using word_ao_absorbs(5) by blast
  moreover from invs and reachable and `a \<noteq> NULL` have "nodeValid s a" 
    using nodesValid_reachable_imp_nodeValid by blast
  moreover have "(?new_size && scast OCC_FLG = (0::32 word) \<longrightarrow> nodeFree ?new_s a)" 
    apply (simp add: `?new_size = ?new_size_simplified`)
    using MEM_NODE_OCCUPIED_FLAG_not_zero
    by (metis calculation(2) h_val_heap_update hrs_update(1) scast_0 scast_scast_id(2) size_C.size_C_def)
  moreover from `nodeValid s a` have "c_guard a \<and>
       unat_ptr a + 8 + unat ((?new_size && scast (~~OCC_FLG)) * 8) 
        \<le> ( if ((node_next ?new_s a) \<noteq> NULL) then unat_ptr (node_next ?new_s a) else 2 ^ LENGTH(32)) 
        \<and> unat (?new_size && scast (~~OCC_FLG)) * 8 < 2 ^ LENGTH(32)" 
    unfolding nodeValid_def
    apply (subst `node_size s a && scast (~~ OCC_FLG) =
        ?new_size  && scast (~~OCC_FLG)`)
    apply (subst ` node_next ?new_s a = node_next s a`)
    using calculation(1)
    by (metis next_C.next_C_def sable_isa.updated_node_val)       
  moreover have "node_next ?new_s a \<noteq> NULL \<longrightarrow> a < node_next ?new_s a \<and> a+\<^sub>p1 \<le> node_next ?new_s a"
    using  `nodeValid s a`
    apply (subst `node_next ?new_s a = node_next s a`)+ by (meson nodeValid_def)     
  ultimately have "nodeValid ?new_s a" unfolding nodeValid_def by presburger 
  moreover have hrs_the_same_after_a:
    "c_guard (a +\<^sub>p 1) \<Longrightarrow> \<forall> x. x \<ge> ptr_val (a +\<^sub>p 1) \<longrightarrow> hrs_the_same_at s ?new_s x"
    using updated_node_hrs_the_same_elsewhere_incorrect by simp
  have next_eq:"node_next ?new_s a = node_next s a" using updated_node_next by fast
      
  have hrs_the_same_except_a:"\<forall>p. p \<notin> ptr_span a \<longrightarrow> hrs_the_same_at s ?new_s p"
    using updated_node_hrs_the_same_elsewhere_correct by blast   
  {
    assume "node_next s a = NULL"
    hence "node_next ?new_s a = NULL" using next_eq by presburger
    hence "nodesValid ?new_s a" using `nodeValid ?new_s a` by simp
  } moreover {
    assume "node_next s a \<noteq> NULL"
    hence "node_next s a > a" using `nodeValid s a` unfolding nodeValid_def by meson
    have "nodesValid s (node_next s a)" 
      using `nodesValid s a` `node_next s a \<noteq> NULL`
      using nodesValid.simps by blast
    have "node_next s a \<ge> (a +\<^sub>p 1)" using `nodeValid s a` `node_next s a \<noteq> NULL`
      unfolding nodeValid_def by meson
        
    have "\<forall>p \<in> ptr_span a. unat p < unat_ptr a + 8" 
      using intvl_upper_bound by auto
    moreover from `nodeValid s a` `node_next s a \<noteq> NULL`
    have "unat_ptr (node_next s a) \<ge> unat_ptr a + 8"
      using `nodeValid s a` `node_next s a \<noteq> NULL` 
      apply simp apply (frule nodeValid_next_val) by auto
    ultimately have "\<forall> p. p \<ge> ptr_val (node_next s a) \<longrightarrow>  p \<notin> ptr_span a"
      by (meson \<open>a < node_next s a\<close> \<open>nodeValid s a\<close> \<open>nodesValid s (node_next s a)\<close> 
          le_less_trans less_irrefl ptr_less_simp nodeValid_imp_range_l nodesValid.simps(1))
        
    hence hrs_the_same_after_a:
      "\<forall> p. p \<ge> ptr_val (node_next s a) \<longrightarrow> hrs_the_same_at s ?new_s p"
      using hrs_the_same_except_a by simp
    with `nodesValid s (node_next s a)` 
    have "nodesValid ?new_s (node_next s a)"     
      using nodesValid_heaps_eq_imp_nodesValid by blast
    hence "nodesValid ?new_s (node_next ?new_s a)" using next_eq by argo
    hence "nodesValid ?new_s a" using `nodeValid ?new_s a`  nodesValid.simps by blast
  }
  ultimately have "nodesValid ?new_s a" by blast
  moreover have hrs_the_same_before_a: "\<forall> p. p< ptr_val a \<longrightarrow> hrs_the_same_at s ?new_s p" 
    apply (subgoal_tac "\<forall> p \<in> ptr_span a. p \<ge> ptr_val a")
    using hrs_the_same_except_a apply force apply auto
    using `c_guard a` unfolding c_guard_def c_null_guard_def apply auto
    by (erule zero_not_in_intvl_lower_bound, assumption)
  hence hrs_the_same_heap_to_a:
    "\<forall>p. p\<ge> ptr_val ?heap_node \<and> p < ptr_val a \<longrightarrow> hrs_the_same_at s ?new_s p"
    by blast
  have "\<forall> p \<in> set (path ?new_s ?heap_node a). nodeValid ?new_s p" 
    using nodesValid_heaps_eq_nodeValid_in_path
    using `nodesValid s ?heap_node` hrs_the_same_heap_to_a
      `reachable s ?heap_node a` `a \<noteq> NULL` 
    by blast
  have "reachable ?new_s ?heap_node a" 
    using hrs_the_same_heap_to_a `reachable s ?heap_node a` `a \<noteq> NULL`      
    sorry    
  from reachable have "a \<ge> ?heap_node" 
    using `a \<noteq> NULL`
    using reachable_helper2 by presburger
  moreover {assume "a > ?heap_node"
    hence "a \<noteq> ?heap_node" by simp
    hence "node_next s ?heap_node > ?heap_node"
      using `a > ?heap_node` reachable reachable.elims(2)
    proof - (* sledgehammered *)
      { assume "next_C (h_val (hrs_mem (t_hrs_' s)) ?heap_node) \<noteq> a"
        then have "?heap_node \<noteq> a \<and> ?heap_node \<noteq> a \<and> next_C (h_val (hrs_mem (t_hrs_' s)) ?heap_node) \<noteq> a"
          using \<open>a \<noteq> ?heap_node\<close> by presburger
        then have ?thesis
          using reachable sable_isa.reachable.elims(2) by blast }
      then show ?thesis
        using \<open>?heap_node < a\<close> by blast
    qed 
    have "node_next s ?heap_node \<le> a"
      using reachable reachable_next_le_to `a \<noteq> NULL` `a \<noteq> ?heap_node`
      by blast
    from `nodeValid s ?heap_node` 
    have "unat_ptr ?heap_node + 8 \<le> unat_ptr (node_next s ?heap_node)"
      using `node_next s ?heap_node > ?heap_node`
      apply (simp add: ptr_le_simp ptr_less_simp)
      apply (drule nodeValid_next_val)
      by auto
    hence "unat_ptr ?heap_node + 8 \<le> unat_ptr a"
      using `node_next s ?heap_node \<le> a`
      using le_trans ptr_le_simp word_le_nat_alt by blast
    moreover have "\<forall>p \<in> ptr_span ?heap_node . unat p < unat_ptr ?heap_node + 8"
      apply (subst eight_eq_eight[THEN sym])
      apply auto
      by (erule intvl_upper_bound)
    ultimately have "\<forall>p \<in> ptr_span a. p \<notin> ptr_span ?heap_node"
      apply auto
      apply (subgoal_tac "p \<ge> ptr_val a")
       apply (meson le_def le_trans word_le_nat_alt)
      using `c_guard a` unfolding c_guard_def c_null_guard_def
      apply auto
      apply (erule zero_not_in_intvl_lower_bound) by assumption
    hence "\<forall>p \<in> ptr_span ?heap_node. hrs_the_same_at s ?new_s p"
      using hrs_the_same_except_a by blast
    hence heap_node_the_same:"node_val s ?heap_node = node_val ?new_s ?heap_node"
      using hrs_the_same_nodes_the_same by blast
    hence "node_next ?new_s ?heap_node \<le> a"
      using `node_next s ?heap_node \<le> a` by simp
    hence "?heap_node \<in> set (path ?new_s ?heap_node a)" 
      using path.simps(2)
      apply (subgoal_tac "?heap_node \<noteq> NULL") 
       apply (subgoal_tac "?heap_node < node_next ?new_s ?heap_node")
        apply fastforce
      using `?heap_node < node_next s ?heap_node` heap_node_the_same apply simp
      using `c_guard ?heap_node` c_guard_NULL by fast          
    hence "nodeValid ?new_s ?heap_node"
      using `\<forall> p \<in> set (path ?new_s ?heap_node a). nodeValid ?new_s p`
      by fast
    have "nodesValid ?new_s ?heap_node" using path_nodeValid_reachable_imp_nodesValid
      using `\<forall> p \<in> set (path ?new_s ?heap_node a). nodeValid ?new_s p`
        `nodeValid ?new_s ?heap_node`
        `reachable ?new_s ?heap_node a`
        `nodesValid ?new_s a` by fast
  }
  moreover{
    assume "?heap_node = a"
    hence "nodesValid ?new_s ?heap_node"
      using `nodesValid ?new_s a` by simp
  }    
  ultimately show "nodesValid ?new_s ?heap_node" by fastforce
next 
  fix a::"mem_node_C ptr"
  fix s::globals
  let ?node_size_masked = "node_size s a && scast (~~ OCC_FLG)"
  let ?new_size =  "((size_bytes >> 3) + 1 || scast OCC_FLG)"
  let ?new_size_masked = "?new_size && scast (~~ OCC_FLG)"
  let ?new_next = "a +\<^sub>p uint ( 2 + (size_bytes >>3) )"
  let ?new_next_size = "(?node_size_masked - (2 + (size_bytes >> 3))) && scast (~~ OCC_FLG)"
  let ?next = "node_next s a"
  let ?new_s_real = "(t_hrs_'_update
          (hrs_mem_update
            (heap_update a (mem_node_C ?new_size ?new_next)) \<circ>
           hrs_mem_update
            (heap_update ?new_next (mem_node_C ?new_next_size ?next)))
          s)"
  let ?new_s = 
    "(update_node (update_node s ?new_next (mem_node_C ?new_next_size ?next)) a (mem_node_C ?new_size ?new_next))"   
  let ?heap_node = "(ptr_coerce heap) :: (mem_node_C ptr)"
  assume nodesValid:"nodesValid s (ptr_coerce heap)"
    and "reachable s (ptr_coerce heap) a"
    and "(size_bytes >> 3) + 1  \<le> ?node_size_masked"
    and "node_size s a && scast OCC_FLG = 0"
    and "(size_bytes >> 3) + 1  < ?node_size_masked"
    and "c_guard a"
    and "a \<noteq> NULL"
    and "c_guard ?new_next"
  from nodesValid have "a \<ge> (ptr_coerce heap)" 
    using `reachable s (ptr_coerce heap) a` `a \<noteq> NULL`
      reachable_helper2 by blast
  have "1 + uint (1 + (size_bytes >>3)) < 2 ^ LENGTH(32)" sorry     
  hence "uint (2 + (size_bytes >>3) ) =  1 + uint (1 + (size_bytes >>3))" by uint_arith
  hence "ptr_val a + of_int( (uint (2 + (size_bytes >>3) )) * xx) = 
         ptr_val a + of_int( (1 + uint ((size_bytes >>3) + 1)) * xx)" by simp 
  hence "a +\<^sub>p uint ( 2 + (size_bytes >>3) ) = (a +\<^sub>p 1) +\<^sub>p uint ((size_bytes >>3)+ 1)" 
    unfolding ptr_add_def by simp 
      
  have "?new_next \<noteq> NULL" using `c_guard ?new_next` c_guard_NULL by auto
  have "nodeValid s a" using nodesValid `reachable s (ptr_coerce heap) a` `a \<noteq> NULL`
    using nodesValid_reachable_imp_nodeValid by blast 
  have new_s_simp[simp]: "?new_s = ?new_s_real" by simp
  have new_size[simp]: "node_size ?new_s a= ?new_size " by (metis updated_node_size)
  have new_next[simp]: "node_next ?new_s a= ?new_next " by (metis updated_node_next)
      
  have "\<forall>p \<ge> ptr_val ?new_next. hrs_the_same_at s ?new_s p" sorry    
  have "?next \<noteq> NULL \<longrightarrow> ?next > a" using `nodeValid s a` nodeValid_def by meson
  have "?next = node_next ?new_s ?new_next"  sorry (* easy *)
  have "?new_next_size = node_size_masked ?new_s ?new_next " sorry   (* easy *) 
  have "unat ((size_bytes >> 3) + 1) * 8 < 2 ^ LENGTH(32)"
    apply (subgoal_tac "unat ?node_size_masked * 8 < 2 ^ LENGTH(32)")
    using `(size_bytes >> 3) + 1 < ?node_size_masked` 
     apply unat_arith
    using `nodeValid s a` unfolding nodeValid_def by meson
  have "unat ?node_size_masked * 8 < 2 ^ LENGTH(32)"
    using `nodeValid s a` unfolding nodeValid_def by meson 
  hence "unat (((size_bytes >> 3) + 1) * 8) = unat ((size_bytes >> 3) + 1) * 8"
    using \<open>unat ((size_bytes >> 3) + 1) * 8 < 2 ^ LENGTH(32)\<close>
    by (metis  sable_isa.eight_eq_eight unat_of_nat_eq word_arith_nat_mult)
  have "unat (?node_size_masked * 8) = unat ?node_size_masked * 8"
    using `unat ?node_size_masked * 8 < 2 ^ LENGTH(32)`
    by (metis  sable_isa.eight_eq_eight unat_of_nat_eq word_arith_nat_mult)   
      
  {
    assume "?next \<noteq> NULL"
    hence "?next > a" using `?next \<noteq> NULL \<longrightarrow> ?next > a` by fast
        
    have "unat ?node_size_masked * 8 = unat (?node_size_masked * 8)"
      using \<open>nodeValid s a\<close> unfolding nodeValid_def Let_def
      by (metis sable_isa.eight_eq_eight unat_of_nat_eq word_arith_nat_mult)    
    have 1:"unat_ptr a + 8 + unat ?node_size_masked * 8 \<le> unat_ptr ?next" 
      using `nodeValid s a` `?next \<noteq> NULL` unfolding nodeValid_def Let_def
      apply (subst `unat ?node_size_masked * 8 = unat (?node_size_masked * 8)`)
      by presburger
        
    have "unat ((size_bytes >> 3) + 1) * 8 = unat (((size_bytes >> 3) + 1) * 8)"
      using `unat ((size_bytes >> 3) + 1) * 8 < 2 ^ LENGTH(32)`
      by (metis sable_isa.eight_eq_eight unat_of_nat_eq word_arith_nat_mult)
    have "unat_ptr a + 8 + unat (((size_bytes >> 3) + 1) * 8) = unat_ptr ?new_next" 
      sorry (* proved later *)
    have 2:"unat_ptr a + 8 + unat ((size_bytes >> 3) + 1) * 8 = unat_ptr ?new_next"
      apply (insert `unat_ptr a + 8 + unat (((size_bytes >> 3) + 1) * 8) = unat_ptr ?new_next`)
      by(subst `unat ((size_bytes >> 3) + 1) * 8 = unat (((size_bytes >> 3) + 1) * 8)`)
        
    from `(size_bytes >> 3) + 1  < ?node_size_masked`
    have "unat ((size_bytes >> 3) + 1) * 8 + 8 \<le> unat ?node_size_masked * 8" by unat_arith
    hence "unat_ptr ?next \<ge> unat_ptr ?new_next + 8" 
      using 1 2 by unat_arith
    hence "unat_ptr ?next > unat_ptr ?new_next" by arith
    hence "?next > ?new_next"
      apply (simp add:ptr_less_simp) 
      using unat_less_impl_less by blast
    have "?next \<ge> ?new_next +\<^sub>p1"
      using `unat_ptr ?next \<ge> unat_ptr ?new_next + 8` unfolding ptr_add_def 
      apply (simp only:ptr_val_def ptr_le_simp mem_node_C_size)
      by (metis mult_numeral_1 numeral_One of_int_numeral of_nat_numeral 
          eight_eq_eight unat_addition_le_pres)   
    have "?next > ?new_next \<and> ?next \<ge> ?new_next +\<^sub>p 1 "
      using `?next \<ge> ?new_next +\<^sub>p1` `?next > ?new_next` by presburger
  } note next_new_next_rel = this 
  {
    have "( 2 + (size_bytes >> 3)) && scast OCC_FLG = 0"
      apply(subgoal_tac "2 + (size_bytes >> 3) && mask 31 = 2 + (size_bytes >> 3) ")
       apply(subgoal_tac "scast OCC_FLG && ((mask 31)::32 word) = 0")
        apply (metis (no_types, hide_lams) word_bw_comms(1) word_bw_lcs(1) word_log_esimps(1))  
      unfolding MEM_NODE_OCCUPIED_FLAG_def 
       apply (subgoal_tac "scast (0x80000000 :: 32 signed word) = (1<<31 ::32 word)")
        apply (metis shiftl_mask_is_0)
       apply simp
      apply (subgoal_tac "2 + (size_bytes >> 3)  \<le> mask 31")
       apply (simp add: and_mask_eq_iff_le_mask)
      apply (subgoal_tac "(size_bytes >> 3) \<le> 0x1FFFFFFF")     
      unfolding mask_def apply unat_arith
      by (rule shiftr3_upper_bound)
    hence "2 + (size_bytes >> 3) && scast (~~ OCC_FLG) = 2 + (size_bytes >> 3)"
      by (simp add: sable_isa.l11 sable_isa.mask_sw32_eq_0_eq_x) (* useless? *)
        
    have "8 + unat ?node_size_masked * 8 < 2 ^ LENGTH(32)" 
      using `nodeValid s a` nodeValid_node_size_l3 by blast
    have node_node_size_bound: "unat (ptr_val a) + 8 + unat (?node_size_masked * 8) 
      \<le> (if ?next \<noteq> NULL then unat (ptr_val ?next) else 2 ^ LENGTH(32))" 
      using `nodeValid s a` unfolding nodeValid_def Let_def by simp 
    have node_node_size_bound_weak:"unat (ptr_val a)+ 8+ unat (?node_size_masked* 8) \<le> 2^ LENGTH(32)" 
      using \<open>nodeValid s a\<close> sable_isa.nodeValid_node_size_l1_new by blast
    have "2 + (size_bytes >> 3) \<le> ?node_size_masked"
      using `(size_bytes >> 3) + 1  < ?node_size_masked` by unat_arith
    have "?new_next_size = ?node_size_masked - (2 + (size_bytes >> 3))"
      apply(subgoal_tac "?node_size_masked && (scast OCC_FLG) = 0")
       apply (subgoal_tac "?node_size_masked - (2 + (size_bytes >> 3)) \<le> ?node_size_masked")
        apply(subgoal_tac "(?node_size_masked - (2 + (size_bytes >> 3))) && scast OCC_FLG = 0")
      using sable_isa.mask_sw32_eq_0_eq_x apply blast
      using OCC_FLAG_helper1 apply blast
      using `2 + (size_bytes >> 3) \<le> ?node_size_masked` 
      using word_not_le word_sub_less_iff apply blast
      using OCC_FLG_neg and_and_not
      by (metis (no_types, hide_lams) word_bool_alg.conj_left_commute word_bw_comms(1))
        
    have "8 + ((size_bytes >> 3) + 1) * 8 < 8 + (?node_size_masked ) * 8"
      using `(size_bytes >> 3) + 1  < ?node_size_masked`
      apply (subgoal_tac "8 + unat (?node_size_masked) * 8 < 2 ^ LENGTH(32)")
       apply(subgoal_tac "unat (8 + ((size_bytes >> 3) + 1) * 8) \<le> 8 + unat ((size_bytes >> 3) + 1) * 8")
        prefer 3
      using \<open>8 + unat (?node_size_masked ) * 8 < 2 ^ LENGTH(32)\<close> apply linarith
       apply (subgoal_tac "unat (8 + ?node_size_masked * 8) = 8 + unat ?node_size_masked * 8")
        prefer 2
      using \<open>nodeValid s a\<close>
        apply (metis (no_types) nodeValid_def eight_eq_eight unat_add_lem unat_mult_lem)
       apply (subgoal_tac "8 + unat ((size_bytes >> 3) + 1) * 8 < 8 + unat (?node_size_masked) * 8")
        apply (simp add: word_less_nat_alt)
       defer
       apply (subgoal_tac "unat (8 + ((size_bytes >> 3) + 1) * 8) \<le> unat 8 + unat (((size_bytes >> 3) + 1) * 8)")
        prefer 2
      using unat_add_le apply blast 
    proof - (* sledgehammered *)
      have f1: "\<And>w. unat (8 + (w::32 word)) \<le> 8 + unat w"
        by (metis sable_isa.eight_eq_eight unat_add_le)
      then have "\<And>w. unat (8 + (w::32 word)) \<le> 8 + 2 ^ len_of (TYPE(32)::32 itself)"
        by (meson add_le_cancel_left le_trans nat_less_le unat_lt2p)
      then have "\<And>n w. n \<le> 8 + 2 ^ len_of (TYPE(32)::32 itself) \<or> \<not> n \<le> unat (8 + (w::32 word))"
        using le_trans by blast
      then show "unat (8 + ((size_bytes >> 3) + 1) * 8) \<le> 8 + unat ((size_bytes >> 3) + 1) * 8"
        using f1 by (metis (no_types) add_le_cancel_left nat_le_linear nat_less_le eight_eq_eight unat_mult_lem)
    next 
      have f1: "\<And>w wa. nat (uint (w::32 word)) < nat (uint wa) \<or> \<not> w < wa"
        by (simp add: unat_def word_less_nat_alt)
      have "1 + (size_bytes >> 3) < scast (~~ OCC_FLG) && node_size s a"
        by (metis \<open>(size_bytes >> 3) + 1 < node_size s a && scast (~~ OCC_FLG)\<close> add.commute word_bw_comms(1))
      then have "8 + 8 * nat (uint (1 + (size_bytes >> 3))) < 8 + 8 * nat (uint (scast (~~ OCC_FLG) && node_size s a))"
        using f1 by auto
      then show "8 + unat ((size_bytes >> 3) + 1) * 8 < 8 + unat (size_C (h_val (hrs_mem (t_hrs_' s)) a) && scast (~~ OCC_FLG)) * 8"
        by (simp add: add.commute unat_def word_bw_comms(1))
    qed
      
    hence "unat (ptr_val a) + unat (8 + ((size_bytes >> 3) + 1) * 8) < 2 ^ LENGTH(32)"
      using node_node_size_bound_weak by unat_arith
    hence 1:"unat (ptr_val a + (0x10 + (size_bytes >> 3) * 8)) =
         unat (ptr_val a) + unat (0x10 + (size_bytes >> 3) * 8)"
      apply simp
      using unat_add_lem by fastforce
        
    have "?node_size_masked * 8 \<ge>  0x10 + (size_bytes >> 3) * 8"
      using `(size_bytes >> 3) + 1  < ?node_size_masked`
      using `2 + (size_bytes >> 3) \<le> ?node_size_masked`
      apply (subgoal_tac "unat ?node_size_masked * unat (8::32 word) < 2 ^ LENGTH(32)") defer 
      using `8 + unat ?node_size_masked * 8 < 2 ^ LENGTH(32)` apply unat_arith
      apply (subgoal_tac "(2 + (size_bytes >> 3)) * 8 \<le> ?node_size_masked * 8") defer
       apply (rule word_mult_le_mono1)
      by auto
        
    hence 2: "unat(?node_size_masked * 8) \<ge>  unat (0x10 + (size_bytes >> 3) * 8)"
      using word_le_nat_alt by blast
        
    have 3: "unat (?node_size_masked * 8 - (0x10 + (size_bytes >> 3) * 8)) =
      unat (?node_size_masked * 8) - unat ((0x10 + (size_bytes >> 3) * 8))"
      using `?node_size_masked * 8 \<ge>  0x10 + (size_bytes >> 3) * 8`
      using unat_sub by fast
        
    have "unat_ptr a + 8 + unat (?node_size_masked * 8) = 
          unat_ptr ?new_next + 8 + unat ((?node_size_masked - (2 + (size_bytes >> 3))) * 8)"
      unfolding ptr_add_def
      apply (simp)
      by (simp add:1 2 3)
        
    hence "unat_ptr ?new_next + 8 + unat (?new_next_size * 8) =
          unat_ptr a + 8 + unat (?node_size_masked * 8)"
      apply (subst `?new_next_size = (?node_size_masked - (2 + (size_bytes >> 3)))`)
      by (rule sym)
        
    hence "unat_ptr ?new_next + 8 + unat (?new_next_size * 8) \<le> 
            (if ?next \<noteq> NULL then unat_ptr ?next else 2 ^ LENGTH(32))" 
      using node_node_size_bound by simp
        
    hence "unat_ptr ?new_next + 8 + unat (?new_next_size * 8) \<le> 
            (if node_next ?new_s ?new_next \<noteq> NULL then unat_ptr (node_next ?new_s ?new_next) else 2 ^ LENGTH(32))"
      using `?next = node_next ?new_s ?new_next` by presburger
        
    have "nodeFree s a" 
      using `node_size s a && scast OCC_FLG = 0` `nodeValid s a` sorry (* easy *)
        
    have "unat (node_size_masked ?new_s ?new_next) * 8 < 2 ^ LENGTH(32)" sorry 
        
    have "nodeFree ?new_s ?new_next"
      unfolding nodeFree_def Let_def
      using `\<forall>p \<ge> ptr_val ?new_next. hrs_the_same_at s ?new_s p`        
    proof-
      have "unat (ptr_val ( a +\<^sub>p 1)) + unat ?node_size_masked * 8 \<le> 2 ^ LENGTH(32)"
        using `nodeValid s a` nodeValid_node_size_l2 by fast
      have "\<forall>p \<in> {ptr_val (a +\<^sub>p 1)..+unat ?node_size_masked * size_of TYPE(mem_node_C)}.
              snd (hrs_htd (t_hrs_' s) p) = Map.empty" using `nodeFree s a` 
        by (simp add: sable_isa.nodeFree_def)
      with `unat (ptr_val ( a +\<^sub>p 1)) + unat ?node_size_masked * 8 \<le> 2 ^ LENGTH(32)`
      have 1:"\<forall>p. p \<ge> ptr_val (a +\<^sub>p 1) \<and> unat p < unat_ptr (a +\<^sub>p 1) + unat ?node_size_masked * size_of TYPE(mem_node_C) \<longrightarrow>
                snd (hrs_htd (t_hrs_' s) p) = Map.empty"
        by (simp add: sable_isa.intvl_no_overflow2) 
        
      {assume "unat_ptr ?new_next + 8 \<ge> 2 ^ LENGTH(32)"
          
        have "unat_ptr a + 8 + unat (((size_bytes >> 3) + 1) * 8) + 8 \<le> 2 ^ LENGTH(32)"
          apply (insert `unat_ptr a + 8 + unat (?node_size_masked * 8) \<le> 2 ^ LENGTH(32)`)
          apply (subst `unat (((size_bytes >> 3) + 1) * 8) = unat ((size_bytes >> 3) + 1) * 8`)
          apply (subst (asm) `unat (?node_size_masked * 8) = unat ?node_size_masked * 8`)  
          using `((size_bytes >> 3) + 1) < ?node_size_masked `
          by unat_arith
            
        have "unat_ptr a + 8 + unat (((size_bytes >> 3) + 1) * 8) = unat_ptr ?new_next" 
          sorry (* proved later *)
        have "unat_ptr a + 8 + unat (((size_bytes >> 3) + 1) * 8) + 8 \<ge> 2 ^ LENGTH(32)"
          using `unat_ptr ?new_next + 8 \<ge> 2 ^ LENGTH(32)`
          apply (subst (asm)`unat_ptr a + 8 + unat (((size_bytes >> 3) + 1) * 8) = unat_ptr ?new_next`[THEN sym])
          by assumption
        hence "unat_ptr a + 8 + unat (((size_bytes >> 3) + 1) * 8) + 8 = 2 ^ LENGTH(32)"
          using `unat_ptr a + 8 + unat (((size_bytes >> 3) + 1) * 8) + 8 \<le> 2 ^ LENGTH(32)`
          by linarith
        have "unat ?node_size_masked * 8 \<ge> unat (((size_bytes >> 3) + 1) * 8) + 8"
          using `?node_size_masked > ((size_bytes >> 3) + 1)`
          apply (subst `unat (((size_bytes >> 3) + 1) * 8) = unat ((size_bytes >> 3) + 1) * 8`)
          by unat_arith
        hence "unat_ptr a + 8 + unat ?node_size_masked * 8 \<ge> 2 ^ LENGTH(32)"
          using `unat_ptr a + 8 + unat (((size_bytes >> 3) + 1) * 8) + 8 \<ge> 2 ^ LENGTH(32)`
          by simp
        hence "unat_ptr a + 8 + unat ?node_size_masked * 8 = 2 ^ LENGTH(32)"
          using `unat_ptr a + 8 + unat (?node_size_masked * 8) \<le> 2 ^ LENGTH(32)`
          apply (subst (asm) `unat (?node_size_masked * 8) = unat ?node_size_masked * 8`)
          by fastforce
        hence "unat (((size_bytes >> 3) + 1) * 8) + 8 = unat ?node_size_masked * 8"
          using `unat_ptr a + 8 + unat (((size_bytes >> 3) + 1) * 8) + 8 = 2 ^ LENGTH(32)`
          by linarith
        hence "unat ((size_bytes >> 3) + 1) * 8 + 8 = unat ?node_size_masked * 8"
          using `unat (((size_bytes >> 3) + 1) * 8) = unat ((size_bytes >> 3) + 1) * 8`
          by linarith
        hence "(unat ((size_bytes >> 3) + 1) + 1) * 8 = unat ?node_size_masked * 8"
          by arith
        hence "((size_bytes >> 3) + 1) + 1 = ?node_size_masked" 
          by unat_arith
        hence "?new_next_size = 0"  
          using `(size_bytes >> 3) + 1  < ?node_size_masked`
          by simp
        hence "array_span (?new_next +\<^sub>p 1) (unat ?new_next_size) = {}" by simp     
        hence "array_span (?new_next +\<^sub>p 1) (unat (node_size_masked ?new_s ?new_next)) = {}"
          using `?new_next_size = node_size_masked ?new_s ?new_next` by argo
        hence "\<forall>p \<in> array_span (?new_next +\<^sub>p 1) (unat (node_size_masked ?new_s ?new_next)).
                 snd (hrs_htd (t_hrs_' ?new_s) p) = Map.empty" by blast
      }
      moreover{
        assume "unat_ptr ?new_next + 8 < 2 ^ LENGTH(32)"
        hence "unat_ptr (?new_next +\<^sub>p 1) = unat_ptr ?new_next + 8"
          unfolding ptr_add_def apply (simp only:ptr_val_def mem_node_C_size)
          using eight_eq_eight
          by (metis mult_numeral_1 numeral_One of_int_1 unat_of_nat_eq 
              word_arith_nat_add word_unat.Rep_inverse)
        have "unat_ptr a + 8 + unat (((size_bytes >> 3) + 1) * 8) = unat_ptr ?new_next" 
          sorry (* proved later *)
        hence "?new_next > a"
          apply (simp add:ptr_less_simp) by unat_arith
            
            
        have "unat (ptr_val (a +\<^sub>p 1)) = unat (ptr_val a + 8)"
          unfolding ptr_add_def by simp
            
        have 2: "ptr_val (?new_next +\<^sub>p 1) > ptr_val ( a +\<^sub>p 1)"  
          apply (rule TypHeapSimple.unat_less_impl_less)
          apply (subst `unat_ptr (?new_next +\<^sub>p 1) = unat_ptr ?new_next + 8`)
          using `?new_next > a`
          apply (simp only:ptr_less_simp)
          apply (subst `unat (ptr_val (a +\<^sub>p 1)) = unat (ptr_val a + 8)`) 
          by unat_arith 
            
        have "unat_ptr a + 8 < 2 ^ LENGTH(32)"
          apply (insert \<open>nodeValid s a\<close>) 
          apply (drule nodeValid_node_size_l2_new)
          using `(size_bytes >> 3) + 1  < ?node_size_masked` by unat_arith
        hence "unat_ptr (a +\<^sub>p 1) = unat_ptr a + 8" 
          unfolding ptr_add_def by unat_arith
            
        have "?new_next_size = (?node_size_masked - (2 + (size_bytes >> 3)))"
          using \<open>?node_size_masked - (2 + (size_bytes >> 3)) && scast (~~ OCC_FLG) =
                 ?node_size_masked - (2 + (size_bytes >> 3))\<close> by blast 
        have "unat ?node_size_masked \<ge> unat (2 + (size_bytes >> 3))" 
          using \<open>2 + (size_bytes >> 3) \<le> ?node_size_masked\<close> word_le_nat_alt by blast  
        hence "unat (?node_size_masked - (2 + (size_bytes >> 3))) = 
               unat ?node_size_masked - unat (2 + (size_bytes >> 3))"
          using `2 + (size_bytes >> 3) \<le> ?node_size_masked` using unat_sub by blast
            
        have "unat (1 + ((size_bytes >>3) + 1)) = unat (1::32 word) + unat ((size_bytes >>3) + 1)"
          using `(size_bytes >> 3) + 1 < ?node_size_masked`
          by unat_arith 
        hence "unat (2 + (size_bytes >>3)) = 1 + unat ((size_bytes >>3) + 1)"
          by simp
            
            
        have "unat (((size_bytes >> 3) + 1) * 8) = unat ((size_bytes >> 3) + 1) * 8"
          using `unat ((size_bytes >> 3) + 1) * 8 < 2 ^ LENGTH(32)`
          by (metis sable_isa.eight_eq_eight unat_mult_lem)
            
        have "unat_ptr ?new_next = unat_ptr a + unat (2 + (size_bytes >>3)) * 8"
          apply (subst `unat (2 + (size_bytes >>3)) = 1 + unat ((size_bytes >>3) + 1)`)
          apply (subst `unat_ptr a + 8 + unat (((size_bytes >> 3) + 1) * 8) = unat_ptr ?new_next`[THEN sym])
          apply (subst `unat (((size_bytes >> 3) + 1) * 8) = unat ((size_bytes >> 3) + 1) * 8`) 
          by auto 
            
            (*            hence "node_next ?new_s ?new_next\<ge> ?new_next +\<^sub>p 1" using `?next = node_next ?new_s ?new_next`     
            sorry 
               *)
        have "unat_ptr (?new_next +\<^sub>p 1) + unat ?new_next_size * size_of TYPE(mem_node_C)
               = unat_ptr (a +\<^sub>p 1) + unat ?node_size_masked * size_of TYPE(mem_node_C)" 
          apply (subst `unat_ptr (?new_next +\<^sub>p 1) = unat_ptr ?new_next + 8`)
          apply (subst `unat_ptr ?new_next = unat_ptr a + unat (2 + (size_bytes >>3)) * 8`)
          apply (subst `unat_ptr (a +\<^sub>p 1) = unat_ptr a + 8`)
          apply (subst `?new_next_size = (?node_size_masked - (2 + (size_bytes >> 3)))`)
          apply (subst `unat (?node_size_masked - (2 + (size_bytes >> 3))) = 
                         unat ?node_size_masked - unat (2 + (size_bytes >> 3))`)
          using `unat ?node_size_masked \<ge> unat (2 + (size_bytes >> 3))`
          by auto
            
        hence 3: "unat_ptr (?new_next +\<^sub>p 1) + unat (node_size_masked ?new_s ?new_next) * size_of TYPE(mem_node_C)
                    = unat_ptr (a +\<^sub>p 1) + unat ?node_size_masked * size_of TYPE(mem_node_C)" 
          using `?new_next_size = node_size_masked ?new_s ?new_next`
          by argo
            
        hence 4: 
          "unat_ptr (?new_next +\<^sub>p 1)+ (unat (node_size_masked ?new_s ?new_next))* size_of TYPE(mem_node_C) \<le> 
           2 ^ LENGTH(32)"
          using \<open>nodeValid s a\<close> nodeValid_node_size_l2 by auto
        hence "\<forall>p. p \<ge> ptr_val (?new_next +\<^sub>p 1) \<and> 
                   unat p<unat_ptr (?new_next +\<^sub>p 1) + (unat (node_size_masked ?new_s ?new_next)) * size_of TYPE(mem_node_C) \<longrightarrow> 
                  p \<ge> ptr_val (a +\<^sub>p 1) \<and> unat p < unat_ptr (a +\<^sub>p 1) + unat ?node_size_masked * size_of TYPE(mem_node_C)"
          using  2 3 by force
            
        hence "\<forall>p \<in> array_span (?new_next +\<^sub>p 1) (unat (node_size_masked ?new_s ?new_next)).
                 p \<ge> ptr_val (a +\<^sub>p 1) \<and> unat p < unat_ptr (a +\<^sub>p 1) + unat ?node_size_masked * size_of TYPE(mem_node_C)"
          using 4 apply clarify          
          apply (drule_tac x=p in intvl_no_overflow2) by blast
        hence "\<forall>p \<in> array_span (?new_next +\<^sub>p 1) (unat (node_size_masked ?new_s ?new_next)).
                 snd (hrs_htd (t_hrs_' ?new_s) p) = Map.empty" 
          using 1 by fastforce
      }
      ultimately show "\<forall>p \<in> array_span (?new_next +\<^sub>p 1) (unat (node_size_masked ?new_s ?new_next)).
                         snd (hrs_htd (t_hrs_' ?new_s) p) = Map.empty" by linarith 
    qed
    hence "node_is_occupied ?new_s ?new_next = 0 \<longrightarrow> nodeFree ?new_s ?new_next" by blast
        
        
    have "node_next ?new_s ?new_next \<noteq> NULL \<longrightarrow>(
          (node_next ?new_s ?new_next) > ?new_next \<and> (node_next ?new_s ?new_next) \<ge> ?new_next +\<^sub>p 1)"
      using next_new_next_rel
      using `?next = node_next ?new_s ?new_next` by argo
        
    have "nodeValid ?new_s ?new_next" 
      using `unat_ptr ?new_next + 8 + unat (?new_next_size * 8) \<le> 
            (if node_next ?new_s ?new_next \<noteq> NULL then unat_ptr (node_next ?new_s ?new_next) else 2 ^ LENGTH(32))`
        `c_guard ?new_next`
        `unat (node_size_masked ?new_s ?new_next) * 8 < 2 ^ LENGTH(32)`
        `node_next ?new_s ?new_next \<noteq> NULL \<longrightarrow>(
          (node_next ?new_s ?new_next) > ?new_next \<and> (node_next ?new_s ?new_next) \<ge> ?new_next +\<^sub>p 1)`
        `node_is_occupied ?new_s ?new_next = 0 \<longrightarrow> nodeFree ?new_s ?new_next`
        `?new_next_size = node_size_masked ?new_s ?new_next`
      unfolding nodeValid_def
      by metis
  }   
    
  {
    assume "?next \<noteq> NULL"
    hence "?next > a" using `?next \<noteq> NULL \<longrightarrow> ?next > a` by fast
        
    hence "\<forall>p \<ge> ptr_val ?next. hrs_the_same_at s ?new_s p"
      using `?next \<noteq> NULL`[THEN next_new_next_rel, THEN conjunct1]
      using `\<forall>p \<ge> ptr_val ?new_next. hrs_the_same_at s ?new_s p`
      by (meson order_less_le_trans ptr_less_def ptr_less_def' word_le_less_eq)
    have "reachable s ?heap_node ?next"
      using `reachable s ?heap_node a` `a \<noteq> NULL` nodesValid 
        nodesValid_reachable_imp_next_reachable by blast 
    hence "nodesValid s ?next"
      using `nodesValid s ?heap_node`
        `?next \<noteq> NULL`
      using nodesValid_reachable_imp_nodesValid by presburger
    hence "nodesValid ?new_s ?next"      
      using nodesValid_heaps_eq_imp_nodesValid
        `\<forall>p \<ge> ptr_val ?next. hrs_the_same_at s ?new_s p` by blast
        
    hence "nodesValid ?new_s ?new_next"
      using `nodeValid ?new_s ?new_next`
      using `nodesValid ?new_s ?next`
      using `?next = node_next ?new_s ?new_next`
      using nodesValid_def' by metis
  }
  moreover{
    assume "?next = NULL"      
    hence "nodesValid ?new_s ?new_next"
      using `nodeValid ?new_s ?new_next`
        `?next = node_next ?new_s ?new_next`
        nodesValid_def' by metis
  }
  ultimately have "nodesValid ?new_s ?new_next" by satx
      
  have "unat ?node_size_masked * 8 < 2 ^ LENGTH(32)" 
    using `nodeValid s a` unfolding nodeValid_def by meson
  have node_size_masked_l_2p32:"(unat ?node_size_masked) * unat (8::32 word) < 2 ^ LENGTH(32)" 
    using `nodeValid s a` unfolding nodeValid_def apply(subst eight_eq_eight) by metis
  hence "((size_bytes >> 3) + 1) * 8 < ?node_size_masked * 8"
    using `(size_bytes >> 3) + 1  < ?node_size_masked`
    by (metis eight_eq_eight unat_0 word_gt_0_no word_mult_less_mono1 zero_neq_numeral)          
  moreover have "unat_ptr a + 8 + unat (?node_size_masked * 8) \<le> 2 ^ LENGTH(32)"
    using `nodeValid s a` nodeValid_node_size_l1_new by fast 
  ultimately have "unat_ptr a + 8 + unat ( ((size_bytes >>3) +1) * 8) <  2 ^ LENGTH(32)"
    using `(size_bytes >>3) +1 < ?node_size_masked` `unat ?node_size_masked * 8 < 2 ^ LENGTH(32)`
    by unat_arith

  have "((size_bytes >> 3) + 1) && scast OCC_FLG = 0"
    apply(subgoal_tac "(size_bytes >> 3) + 1 && mask 31 = (size_bytes >> 3) + 1")
    apply(subgoal_tac "scast OCC_FLG && ((mask 31)::32 word) = 0")
    apply (metis (no_types, hide_lams) word_bw_comms(1) word_bw_lcs(1) word_log_esimps(1))  
    unfolding MEM_NODE_OCCUPIED_FLAG_def 
    apply (subgoal_tac "scast (0x80000000 :: 32 signed word) = (1<<31 ::32 word)")
    apply (metis shiftl_mask_is_0)
    apply simp
    apply (subgoal_tac "(size_bytes >> 3) + 1 \<le> mask 31")
    apply (simp add: and_mask_eq_iff_le_mask)
    apply (subgoal_tac "(size_bytes >> 3) \<le> 0x1FFFFFFF")     
    unfolding mask_def apply unat_arith
    by (rule shiftr3_upper_bound)      
      
  hence new_size_eq:"?new_size_masked = (size_bytes >> 3) + 1"
    by (simp add: sable_isa.l11 sable_isa.mask_sw32_eq_0_eq_x)
      
  have "unat_ptr a + 8 + unat (((size_bytes >> 3) + 1) * 8) =
        unat (ptr_val a + 8 + ((size_bytes >> 3) + 1) * 8)"
    apply(insert `unat_ptr a + 8 + unat (((size_bytes >> 3) + 1) * 8) < 2 ^ LENGTH(32)`) 
    using  unat_add_lem_3
    by (metis sable_isa.eight_eq_eight) 
  hence "unat_ptr a + 8 + unat (?new_size_masked * 8) = unat_ptr (a +\<^sub>p uint (?new_size_masked + 1))"
    apply (simp only: new_size_eq)
    unfolding ptr_add_def apply (simp only: mem_node_C_size)
    unfolding ptr_val_def apply (simp only: of_int_uint)
    apply (subst (2) Rings.comm_semiring_class.distrib)
    by auto 
  hence "unat_ptr a + 8 + unat (((size_bytes >> 3) + 1) * 8) = unat_ptr ?new_next" 
    using new_size_eq by auto    
  {      
    from `unat_ptr a + 8 + unat (((size_bytes >> 3) + 1) * 8) = unat_ptr ?new_next`
    have "unat_ptr ?new_next \<ge> unat_ptr a + 8"
      unfolding ptr_add_def
      by (simp add:ptr_less_simp) 
    hence "?new_next \<ge> a +\<^sub>p 1" 
      unfolding ptr_add_def
      apply (simp add:ptr_le_simp) 
      apply (subst (asm) eight_eq_eight[THEN sym])
      by(erule unat_addition_le_pres)  
    moreover have "?new_next > a" 
      using `unat_ptr a + 8 + unat (((size_bytes >> 3) + 1) * 8) = unat_ptr ?new_next`
      apply(simp only:ptr_less_simp)
      by (simp add: word_less_nat_alt)
    ultimately have new_next_g_a:"?new_next > a \<and> ?new_next \<ge> (a +\<^sub>p 1)" 
      using order_less_le_trans by auto 
  } note new_next_g_a= this
  moreover{
    from `unat_ptr a + 8 + unat (((size_bytes >> 3) + 1) * 8) = unat_ptr ?new_next`
    have "unat_ptr a + 8 + unat (((size_bytes >> 3) + 1) * 8) \<le> unat_ptr ?new_next" 
      by auto         
    hence  "unat_ptr a + 8 + unat (?new_size_masked * 8) \<le> unat_ptr ?new_next"
      using new_size_eq by argo
    hence "unat_ptr a + 8 + unat (?new_size_masked * 8)
       \<le> (if ?new_next \<noteq> NULL then unat_ptr ?new_next else 2 ^ LENGTH(32))"
      using `?new_next \<noteq> NULL` by simp
    moreover{ have "(unat ?node_size_masked) * 8 < 2 ^ LENGTH(32)" 
        using `nodeValid s a` unfolding nodeValid_def by meson  
      with `(size_bytes >> 3) + 1  < ?node_size_masked` 
      have "(unat ?new_size_masked) * 8 < 2 ^ LENGTH(32)"
        apply (subst new_size_eq) apply(drule unat_mono)  by linarith
    }
    moreover{
      have "node_is_occupied ?new_s a = scast OCC_FLG"
        by (metis (no_types) sable_isa.updated_node_size word_ao_absorbs(5))
      hence "node_is_occupied ?new_s a \<noteq> 0" unfolding MEM_NODE_OCCUPIED_FLAG_def by auto 
    }
    moreover  have "(?new_next \<noteq> NULL \<longrightarrow> ?new_next > a \<and> ?new_next \<ge> a +\<^sub>p 1)" 
      using new_next_g_a by auto
    ultimately have "nodeValid ?new_s a" using `c_guard a` unfolding nodeValid_def
      using new_next new_size by auto        
  }      
  ultimately have "nodesValid ?new_s a" (* !! *)
    using new_next `nodesValid ?new_s ?new_next` 
    using nodesValid_trans_back by presburger
  have "\<forall> p. p < ptr_val a \<longrightarrow> hrs_the_same_at s ?new_s p"
    apply clarify
    apply (rule updated_node_blahblah_2) using new_next_g_a 
    apply (subgoal_tac "ptr_val a < ptr_val ( a +\<^sub>p uint (2 + (size_bytes >> 3)))")
    by (auto simp:ptr_less_def' ptr_less_def)
  hence hrs_the_same_heap_to_a:
    "\<forall> p. p \<ge> ptr_val (ptr_coerce heap) \<and> p < ptr_val a \<longrightarrow> hrs_the_same_at s ?new_s p"
    by simp   
  hence paths_the_same:"path s (ptr_coerce heap) a = path ?new_s (ptr_coerce heap) a"
    by (rule heaps_eq_imp_paths_eq)
      
  moreover have new_s_path_nodeValid:"\<forall> p \<in> set (path ?new_s ?heap_node a). nodeValid ?new_s p" 
    using nodesValid_heaps_eq_nodeValid_in_path
    using `nodesValid s ?heap_node` hrs_the_same_heap_to_a
      `reachable s ?heap_node a` `a \<noteq> NULL` 
    by blast    
      
  moreover have "reachable ?new_s ?heap_node a"
    using `reachable s (ptr_coerce heap) a`
      `nodesValid s (ptr_coerce heap)`
      hrs_the_same_heap_to_a
      `a \<noteq> NULL`
      hrs_the_sam_nodesValid_reachable_imp_reachable by blast     
      
  {assume "a > ptr_coerce heap" 
    hence "a \<noteq> ptr_coerce heap" by simp
    hence "(ptr_coerce heap) \<in> set (path s (ptr_coerce heap) a)" 
      using `nodesValid s (ptr_coerce heap)` `reachable s (ptr_coerce heap) a` `a \<noteq> NULL` 
        nodesValid_reachable_imp_in_path by fast
    hence "(ptr_coerce heap) \<in> set (path ?new_s (ptr_coerce heap) a)"
      using paths_the_same by argo
    hence  "nodeValid ?new_s (ptr_coerce heap)" using new_s_path_nodeValid by fast
  } moreover
  {assume "\<not>a > ptr_coerce heap"
    hence "a = ptr_coerce heap" using ` a \<ge>  ( ptr_coerce heap)` by simp
    hence "nodeValid ?new_s (ptr_coerce heap)" using `nodeValid ?new_s a` by simp
  }
  ultimately have "nodeValid ?new_s (ptr_coerce heap)" by blast
      
  have "nodesValid ?new_s ?heap_node" 
    using `nodesValid ?new_s a`
      `nodeValid ?new_s ?heap_node`
      `reachable ?new_s ?heap_node a`
      new_s_path_nodeValid 
    apply auto
    apply (rule path_nodeValid_reachable_imp_nodesValid)
    by blast+
  thus "nodesValid ?new_s_real (ptr_coerce heap)" by auto
qed


  
lemma alloc'_hoare_helper:
  fixes size_bytes heap
  assumes n:"size_of TYPE('a) \<le> unat size_bytes"
    and align: "align_of TYPE('a) dvd align_of TYPE(mem_node_C)"
  shows "\<And>(node::mem_node_C ptr) s::globals.
       heap_invs s heap \<Longrightarrow>
       reachable s (ptr_coerce heap) node \<Longrightarrow>
       (size_bytes >> (3::nat)) + (1::32 word)
       \<le> size_C (h_val (hrs_mem (t_hrs_' s)) node) && scast (~~ OCC_FLG) \<Longrightarrow>
       size_C (h_val (hrs_mem (t_hrs_' s)) node) && scast OCC_FLG = (0::32 word) \<Longrightarrow>
       node \<noteq> NULL \<Longrightarrow>
       c_guard node \<Longrightarrow>      
       ptr_val (node +\<^sub>p (1::int)) \<noteq> (0::32 word) \<Longrightarrow>
       heap_ptr_valid (ptr_retyp ((ptr_coerce (node +\<^sub>p (1)))::'a::mem_type ptr) (hrs_htd (t_hrs_' s)))
        ((ptr_coerce (node +\<^sub>p (1::int))):: 'a ptr)"
  unfolding heap_invs_def
proof -
  fix s :: globals fix node ::"mem_node_C ptr"
  let ?ptrc = "ptr_coerce (node  +\<^sub>p 1) :: 'a ptr"
  let ?node_size = "size_C (h_val (hrs_mem (t_hrs_' s)) node) && scast (~~ OCC_FLG) :: 32 word"
  let ?blocks = "(size_bytes >> 3) + 1 :: 32 word"
  let ?heap_ptr = "ptr_coerce heap :: mem_node_C ptr"
  assume "ptr_val (node +\<^sub>p 1) \<noteq> 0" 
    and invs: "nodesValid s (ptr_coerce heap)"
    and blocks_size: "?blocks \<le> ?node_size"
    and "reachable s (ptr_coerce heap) node"
    and node_empty: "size_C (h_val (hrs_mem (t_hrs_' s)) node) && scast OCC_FLG = 0"
    and "node \<noteq> NULL"
    and "c_guard node"
    and "ptr_val (node +\<^sub>p 1) \<noteq> 0"
  have "nodeValid s node"  using `reachable s (ptr_coerce heap) node` \<open>node \<noteq> NULL\<close>
    using invs nodesValid_reachable_imp_nodeValid by blast
  hence nodeFree:"nodeFree s node" using node_empty unfolding nodeValid_def by meson 
  hence empty: "\<forall>p\<in>{ptr_val (node +\<^sub>p 1)..+unat ?node_size * 8}.
                            snd (hrs_htd (t_hrs_' s) p) = Map.empty"
    unfolding nodeFree_def by auto
  have node_size: "unat_ptr (node +\<^sub>p 1) + unat (?node_size * 8) \<le> 2 ^ len_of (TYPE(32))"
    using `nodeValid s node`  sable_isa.nodeValid_node_size_l1 by presburger   
  have "0 \<notin> {ptr_val (node +\<^sub>p 1)..+ unat (?node_size * 8)}"
  proof (rule ccontr)
    assume "\<not> 0 \<notin> {ptr_val (node +\<^sub>p 1)..+ unat (?node_size * 8)}"
    hence "0 \<in> {ptr_val (node +\<^sub>p 1)..+ unat (?node_size * 8)}" by simp
    then obtain k where 0:"0=ptr_val (node +\<^sub>p 1) + of_nat k \<and> k < unat (?node_size * 8)"
      using intvlD by blast
    hence "k \<le> unat (?node_size * 8) -1 " by (simp add: nat_le_Suc_less_imp)
    moreover from node_size have "unat_ptr (node +\<^sub>p 1) + (unat (?node_size * 8) - 1) < 2 ^ len_of (TYPE(32))"
      by unat_arith
    ultimately have "unat_ptr (node +\<^sub>p 1) +  k <  2 ^ len_of (TYPE(32))" by arith
    hence "ptr_val (node +\<^sub>p 1) + of_nat k \<ge> ptr_val (node +\<^sub>p 1)"
      by (metis add.commute add_lessD1 no_olen_add_nat unat_of_nat32 word_bits_def)
    hence "ptr_val (node +\<^sub>p 1) + of_nat k \<noteq> 0" using `ptr_val (node +\<^sub>p 1) \<noteq> 0` by auto
    thus False using 0 by force
  qed 
  hence zero_not_in_node_range:"0 \<notin> {ptr_val (ptr_coerce (node +\<^sub>p (1::int)))..+ unat (?node_size * 8)}" 
    by simp
  have "unat ?node_size * 8 < 2 ^ len_of (TYPE(32))"
    using `nodeValid s node` unfolding nodeValid_def by meson
  show "heap_ptr_valid (ptr_retyp ?ptrc (hrs_htd (t_hrs_' s))) ?ptrc"
    unfolding heap_ptr_valid_def c_guard_def  
  proof safe
    show "valid_simple_footprint (ptr_retyp ?ptrc (hrs_htd (t_hrs_' s))) (ptr_val ?ptrc)
          (typ_uinfo_t TYPE('a))"
      apply (rule TypHeapSimple.valid_simple_footprint_ptr_retyp) defer
      apply (simp, metis Suc_le_eq mem_type_simps(3) size_of_def)
      apply (simp add: size_of_tag)
    proof safe 
      fix k
      assume "k < size_td (typ_uinfo_t TYPE('a))"
      with `size_of TYPE('a) \<le> unat size_bytes` have "k < unat size_bytes" 
        unfolding size_of_def by unat_arith
      with blocks_size have "k < unat ?node_size * 8" by (simp add: shiftr3_is_div_8, unat_arith)
      hence "ptr_val (ptr_coerce (node +\<^sub>p 1)) + of_nat k \<in> {ptr_val (node +\<^sub>p 1)..+unat ?node_size * 8}"
        by (simp add: intvlI)     
      thus "snd (hrs_htd (t_hrs_' s) (ptr_val (ptr_coerce (node +\<^sub>p 1)) + of_nat k)) = Map.empty"
        using empty by simp
    qed
  next    
    show "ptr_aligned (ptr_coerce (node +\<^sub>p 1) :: 'a ptr)"
      using align `c_guard node` unfolding c_guard_def
      by (metis gcd_nat.trans ptr_aligned_def ptr_aligned_plus ptr_val_ptr_coerce) 
  next
    have range_size_subsumes_range_'a: 
      "{ptr_val (ptr_coerce (node +\<^sub>p (1::int)))..+size_of TYPE('a)}
      \<subseteq>{ptr_val (ptr_coerce (node +\<^sub>p (1::int)))..+ unat size_bytes}"
      by (simp add: intvl_start_le n) 
    have "(2::nat) ^ len_of (TYPE(32)) = 2 ^ 32" by simp
    have "(size_bytes >> 3) + 1 \<le> ?node_size" using blocks_size by simp
    moreover have "unat (8::word32) = 8" by simp
    moreover have "(8:: word32) > 0" by simp
    ultimately have "((size_bytes >> 3) + 1) * 8 \<le> ?node_size * 8" 
      using `unat ?node_size * 8 < 2 ^ len_of (TYPE(32))` word_mult_le_mono1 by fastforce 
    moreover have "((size_bytes >> 3) + 1) * 8 = (size_bytes >> 3) * 8 + 8"  by unat_arith
    have "unat ((size_bytes >> 3) + 1) * 8 < 2 ^ LENGTH(32)"
      using `(size_bytes >> 3) + 1 \<le> ?node_size` `nodeValid s node` 
      unfolding nodeValid_def Let_def by (simp add: le_def word_le_nat_alt) 
    hence "unat size_bytes + 8 < 2 ^ 32" by (simp add: shiftr3_is_div_8 ) unat_arith 
    moreover have "size_bytes < size_bytes + 8"
      using calculation unat_of_nat32 word_bits_conv word_less_nat_alt by fastforce 
    moreover have "(size_bytes >> 3) * 8 + 8 \<ge> size_bytes" 
      apply (simp add: shiftr3_is_div_8) apply (rule l10)
      using \<open>unat (8::32 word) = (8::nat)\<close> calculation(2) by linarith simp      
    ultimately have "size_bytes \<le> ?node_size * 8" by auto 
    hence "{ptr_val (ptr_coerce (node +\<^sub>p 1))..+unat size_bytes}
              \<subseteq> {ptr_val (ptr_coerce (node +\<^sub>p 1))..+ unat (?node_size * 8)}"
      by (simp add: intvl_start_le word_le_nat_alt)
    hence "{ptr_val (ptr_coerce (node +\<^sub>p 1))..+size_of TYPE('a)}
              \<subseteq> {ptr_val (ptr_coerce (node +\<^sub>p (1::int)))..+ unat (?node_size * 8)}"  
      using range_size_subsumes_range_'a by auto   
    hence "0 \<notin> {ptr_val ((ptr_coerce (node +\<^sub>p 1)) :: 'a ptr)..+ size_of TYPE('a)}"
      using zero_not_in_node_range by fast
    thus "c_null_guard (ptr_coerce (node +\<^sub>p 1):: 'a ptr)" unfolding c_null_guard_def by blast  
  qed
qed
  
lemma alloc'_hoare:
  fixes size_bytes :: "32 word"
  assumes align: "align_of TYPE('a) dvd align_of TYPE(mem_node_C)"
    and n: "size_of TYPE('a) \<le> unat size_bytes" and "0 < size_bytes"
  shows "\<lbrace>\<lambda>s. heap_invs s heap\<rbrace> alloc' heap size_bytes
       \<lbrace>\<lambda>r s. let ptr = (ptr_coerce r) :: ('a :: mem_type) ptr in
        ptr_val r \<noteq> 0 \<longrightarrow> heap_ptr_valid (ptr_retyp ptr (hrs_htd (t_hrs_' s))) ptr\<rbrace>"
  unfolding alloc'_def Let_def 
  apply (simp add: h_val_field_from_bytes)
  apply (subst whileLoop_add_inv 
      [where I="\<lambda> (n,r) s. heap_invs s heap  \<and> reachable s (ptr_coerce heap) n
                  \<and> (r=0 \<longrightarrow> n = NULL \<or> ((size_bytes >> 3) + 1
                     \<le> size_C (h_val (hrs_mem (t_hrs_' s)) n) && scast (~~ OCC_FLG))
                  \<and> size_C (h_val (hrs_mem (t_hrs_' s)) n) && scast OCC_FLG = 0)" 
        and M="\<lambda> ((n,y),s). ptr_val n"])
  apply (wp fail'_wp)
  apply (simp add: `0 < size_bytes` h_val_id not_le)
  defer defer
  apply (wp fail'_wp)
  prefer 2
  apply (erule iffD1[OF refl])
  apply (auto simp: `0 < size_bytes`)
  apply wp
  apply auto
    (* FIXME error *)
  apply (rule self_reachable, solves simp)
  apply (drule heap_invs_not_null, solves auto)
  apply (rule self_reachable, solves auto)
  apply (drule one_mask_neg_MNOF_not_zero, solves simp)
  apply (drule heap_invs_not_null, solves auto)
  apply (rule self_reachable, solves auto)
  apply (drule mask_sw32_eq_0_eq_x, solves auto)
  apply (drule heap_invs_not_null, solves auto)
  unfolding heap_invs_def
    (* FIXME: use this: *)
  apply(drule nodesValid_reachable_imp_next_reachable, auto)+
    (*instead of this: apply (drule reachable_trans,solves auto, solves auto)+ *)
  apply (drule one_mask_neg_MNOF_not_zero, solves simp)
    
  apply (drule reachable_trans,solves auto, solves auto)
  apply (drule c_guard_NULL,rule reachable_trans, solves simp, solves simp)
  apply (drule mask_sw32_eq_0_eq_x, solves auto)
  apply (drule c_guard_NULL,drule reachable_trans, solves simp, solves simp)+
  apply (drule one_mask_neg_MNOF_not_zero, solves simp)
  apply (drule c_guard_NULL,drule reachable_trans, solves simp, solves simp)+
  apply (drule mask_sw32_eq_0_eq_x, solves auto)
  apply (drule c_guard_NULL,drule reachable_trans, solves simp, solves simp)
  using n align apply (rule alloc'_hoare_helper, auto)
  using n align apply (rule alloc'_hoare_helper, auto) 
  done
    
    
text \<open> hello! @{thm (lhs) simple_lift_def}  \<close>   
  
thm "valid_simple_footprint_def"
thm "heap_ptr_valid_def"
thm "simple_lift_def"
typ "globals"
print_record "lifted_globals"
value " (s :: globals)"
  (*declare [[show_types]]
declare [[show_consts]]
declare [[show_sorts]]*)
  
lemma alloc_w32_safe: "\<lbrace>\<lambda>s. (liftC lift_global_heap (\<lambda>s. heap_invs s heap)) s\<rbrace>
                       exec_concrete lift_global_heap (alloc' heap 4)
      \<lbrace>\<lambda>r s. ptr_val r \<noteq> 0 \<longrightarrow> is_valid_w32 s ((ptr_coerce r) :: (32 word) ptr)\<rbrace>!"
  apply (rule validNF)
  apply wp
  apply (rule hoare_post_imp)
  prefer 2
  apply (rule alloc'_hoare[where 'a="32 word"])
  apply (auto simp add: align_of_def Let_def)+
  apply (simp add: lifted_globals_ext_simps(6) simple_lift_def)
  using alloc'_hoare[where n=4 and 'a="32 word"] apply (simp add: Let_def
  unfolding validNF_def valid_def
  apply auto
proof -
  fix s a b
  assume "\<forall>g. lift_global_heap s = lift_global_heap g \<longrightarrow> heap_invs g"
    and "\<forall>g. lift_global_heap b = lift_global_heap g \<longrightarrow> heap_invs g"
  hence "heap_invs s" and "heap_invs b" by auto
  oops
    
end
  
end