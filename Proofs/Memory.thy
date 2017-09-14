theory Memory
  imports
    "../AutoCorres/Impl"
    "../lib/ExtraLemmas"
    "./Memory_Nodes"
    "./Memory_ExtraLemmas"
    "$ISABELLE_HOME/src/HOL/Library/LaTeXsugar"    
begin
text \<open>This theory file proves correctness of the heap allocator's alloc() function.
      The required supporting definitions and lemmas come first, they are followed by a lemma
      that states alloc() preserves a set of invariants, and at the end the
      lemma that states that alloc() is correct given the invariants as a precondition
      is proved\<close> 
  
context sable_isa
begin
  
abbreviation "ALIGN_BITS \<equiv> 3"
abbreviation "OCC_FLG \<equiv> MEM_NODE_OCCUPIED_FLAG" 
abbreviation "SZ_mem_node \<equiv> size_of TYPE(mem_node_C)"
  
abbreviation unat_ptr :: "'a ptr \<Rightarrow> nat"
  where "unat_ptr p \<equiv> unat (ptr_val p)"
    
definition
  mem_node_C_guard :: "mem_node_C ptr \<Rightarrow> bool"
  where
    "mem_node_C_guard n \<equiv> c_null_guard n \<and> is_aligned (ptr_val n) ALIGN_BITS"
    
lemma[dest, intro]: "mem_node_C_guard p \<Longrightarrow> c_guard p"
  unfolding mem_node_C_guard_def c_guard_def ptr_aligned_def is_aligned_def
  by (auto simp add: align_of_def, unat_arith)
    
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
  oops    
    
lemma fail'_wp: "\<lbrace>\<lambda>x. True\<rbrace> fail' \<lbrace>Q\<rbrace>"
  unfolding fail'_def FUNCTION_BODY_NOT_IN_INPUT_C_FILE_def by wp
    
    
    (*definition
  init_heap_P :: "unit ptr \<Rightarrow> 32 word \<Rightarrow> globals \<Rightarrow> bool"
where
  "init_heap_P p n s \<equiv> 0 \<notin> {ptr_val p..+unat n} \<and> is_aligned (ptr_val p) ALIGN_BITS \<and>
    (\<forall>node \<in> {ptr_val p..+unat n}. snd (hrs_htd (t_hrs_' s) node) = Map.empty)"*)
    
definition nodeFree :: "globals \<Rightarrow> mem_node_C ptr \<Rightarrow> bool"
  where "nodeFree s node \<equiv>
    (let size = node_size_masked s node in
    \<forall>p \<in> {ptr_val (node +\<^sub>p 1)..+unat size * SZ_mem_node}.
      snd (hrs_htd (t_hrs_' s) p) = Map.empty)"
    
text \<open>the nodeValid predicate defines the constraints on each node that alloc()
      must preserve. It is not defined in the most straightforward fashion possible, but it is
      valid nonetheless\<close>    
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
    
lemma nodeValid_node_node_size_upper_bound:
  "nodeValid s node \<Longrightarrow>  
   unat_ptr node + 8 + unat ((node_size_masked s node) * 8) \<le> 2 ^ LENGTH(32)"
  unfolding nodeValid_def Let_def
  apply (subgoal_tac "unat (ptr_val (next_C (h_val (hrs_mem (t_hrs_' s)) node))) < 2 ^ LENGTH(32)")
   apply (auto simp:if_split)[1]
  by blast
    
lemma nodeValid_node_node_size_upper_bound':
  "nodeValid s node \<Longrightarrow>
   unat_ptr (node +\<^sub>p 1) + unat ((node_size_masked s node) * 8) \<le> 2 ^ LENGTH(32)"
  apply (drule nodeValid_node_node_size_upper_bound)
  unfolding ptr_add_def  
  by unat_arith 
    
lemma nodeValid_node_node_size_upper_bound2:
  "nodeValid s node \<Longrightarrow>  
   unat_ptr node + 8 + unat (node_size_masked s node) * 8 \<le> 2 ^ LENGTH(32)"
  apply (frule nodeValid_node_node_size_upper_bound)
  apply (subgoal_tac "unat (node_size_masked s node) * 8 = unat (node_size_masked s node * 8)")
   apply argo
  unfolding nodeValid_def Let_def
  apply clarify
  apply (simp only:eight_eq_eight[THEN sym])
  apply (subst (asm) unat_mult_lem) 
  by argo
    
lemma nodeValid_node_node_size_upper_bound2':
  "nodeValid s node \<Longrightarrow>  
   unat_ptr (node +\<^sub>p 1) + unat (node_size_masked s node) * 8 \<le> 2 ^ LENGTH(32)"
  apply (drule nodeValid_node_node_size_upper_bound2)
  unfolding ptr_add_def  
  by unat_arith 
    
lemma nodeValid_node_size_upper_bound:
  "nodeValid s node \<Longrightarrow>
     8 + unat (node_size_masked s node) * 8 < 2 ^ LENGTH(32)"
  apply (subgoal_tac "ptr_val node > 0")
   apply (drule nodeValid_node_node_size_upper_bound2)
   apply unat_arith
  unfolding nodeValid_def Let_def apply clarify
  apply (drule c_guard_NULL) 
  apply (subgoal_tac "ptr_val node \<noteq> 0") 
  using word_neq_0_conv apply blast
  by (metis ptr.exhaust ptr_val.ptr_val_def)
    
text \<open>This is essentially the definition of the heap invariants that alloc() must preserve.
      It requires all the nodes in the linked list to be valid\<close>
function 
  nodesValid :: "globals \<Rightarrow> mem_node_C ptr \<Rightarrow> bool" 
  where
    "\<not> (nodeValid s heap_node) \<Longrightarrow> nodesValid s heap_node = False"
  |"nodeValid s heap_node \<and> node_next s heap_node = NULL \<Longrightarrow> nodesValid s heap_node = True"
  |"nodeValid s heap_node \<and> node_next s heap_node \<noteq> NULL \<Longrightarrow> nodesValid s heap_node =
      nodesValid s (node_next s heap_node)" 
        apply auto by blast
termination
  apply (relation "measure (\<lambda> (s,heap). 2 ^ 32 - unat_ptr heap)")
   apply auto
  unfolding nodeValid_def Let_def
  apply (clarsimp simp:ptr_less_simp ptr_le_simp)
  by unat_arith auto
    
text \<open>a simplified definition of nodesValid, equivalent to the real definition\<close>   
lemma nodesValid_def': "nodesValid s heap_node =
  (let next = (node_next s heap_node) in 
    nodeValid s heap_node \<and> (next \<noteq> NULL \<longrightarrow> nodesValid s next))"
  unfolding Let_def
  using nodesValid.simps by blast
    
definition heap_invs :: "globals \<Rightarrow> unit ptr \<Rightarrow> bool"
  where "heap_invs s heap_node \<equiv> nodesValid s (ptr_coerce heap_node)"
    
lemma nodesValid_nodeValid: "nodesValid s n \<Longrightarrow> nodeValid s n"
  apply(subst (asm) nodesValid_def') unfolding Let_def by auto
    
lemma nodesValid_not_null:
  "nodesValid s heap_node \<Longrightarrow> heap_node \<noteq> NULL"
  by (meson c_guard_NULL_simp nodeValid_def nodesValid_def') 
    
lemma heap_invs_not_null :"heap_invs s heap_node \<Longrightarrow> heap_node \<noteq> NULL" 
  unfolding heap_invs_def
  apply (drule nodesValid_not_null) by auto
    
lemma nodesValid_not_next_null:
  "nodesValid s node \<Longrightarrow> \<not> nodesValid s (node_next s node) \<Longrightarrow> (node_next s node) = NULL"
  using nodesValid.elims by auto 
    
text \<open>reachable is a predicate returning true when node `to` is reachable from node `node` in the
      linked list. Its definition is split into multiple cases to make proving totality of the
      function possible, in addition the next node of each node must be at a higher address than
      the node for totality to be provable \<close>    
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
  by (auto simp: ptr_le_simp ptr_less_simp)  
    
lemma reachable_trans2[rule_format]:
  "reachable s node to \<longrightarrow> to \<noteq> NULL \<longrightarrow> node_next s to = NULL \<longrightarrow> 
   reachable s node (node_next s to)"
  apply (rule_tac ?a0.0=s and ?a1.0=node and ?a2.0=to in  reachable.induct)
  by auto
    
text \<open> the memory outside an updated linked list node remains untouched \<close>
lemma updated_node_hrs_the_same_elsewhere:
  assumes x_val:"x \<notin> ptr_span p"
  shows"hrs_the_same_at s (update_node s p new_node) x"
proof-
  let ?xptr = "(Ptr x)::8 word ptr"
  have x[simp] : "ptr_val ?xptr = x" by simp
  hence "ptr_span p \<inter> {ptr_val ?xptr..+size_of TYPE(8 word)} = {}"
    apply simp 
    using intvl_Suc x_val by auto
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
  
lemma dobule_update_heaps_eq_before:
  assumes "x < ptr_val p" and "x < ptr_val q"
    and "c_null_guard p" and "c_null_guard q"
  shows "hrs_the_same_at s (update_node (update_node s p new_node_1) q new_node_2 ) x"
proof-
  let ?halfway_s = "update_node s p new_node_1"
  let ?new_s = "update_node ?halfway_s q new_node_2"
  have "x \<notin> ptr_span p" using `x< ptr_val p` `c_null_guard p`
    unfolding c_null_guard_def
    using zero_not_in_intvl_lower_bound by fastforce
  hence "hrs_the_same_at s ?halfway_s x"
    using updated_node_hrs_the_same_elsewhere by blast
  have "x \<notin> ptr_span q" using `x< ptr_val q` `c_null_guard q`
    unfolding c_null_guard_def
    using zero_not_in_intvl_lower_bound by fastforce   
  hence "hrs_the_same_at ?halfway_s ?new_s x"
    using updated_node_hrs_the_same_elsewhere by blast
  thus "hrs_the_same_at s ?new_s x"  
    using `hrs_the_same_at s ?halfway_s x`
    by simp
qed
  
text \<open>This function returns all the nodes in path from node `node` to node `to` (excluding `to`).
      Each node in the path must be at a higher address than its previous node. In addition to 
      being a reflection of the heap allocator implementation, this requirement makes the path 
      function a total function (a function with a defined value for every combination of parameters).
      Totality is required in Isabelle for all functions \<close>
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
  text \<open> introducing a function that is monotonically decreasing with each recursive call
        is the way to prove wellfoundedness of the relation between recursive parameters,
        which in turn proves totality \<close>
  apply (relation "measure (\<lambda> (s,node,to).2 ^ 32 + unat_ptr to - unat_ptr node)")
   apply (auto simp:ptr_less_simp ptr_le_simp)
  by unat_arith     
    
lemma path_not_empty_node_cond[rule_format]: "set (path s node to) \<noteq> {} \<longrightarrow> 
        node \<noteq> NULL \<and>
        ptr_val node < ptr_val (node_next s node) \<and>
        ptr_val node < ptr_val to \<and> ptr_val (node_next s node) \<le> ptr_val to"
  apply (simp add:ptr_less_simp[THEN sym] ptr_le_simp[THEN sym])
  apply (subst contrapos)
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
    
text \<open>if a valid node is at the last possible place in the address space (2 ^ 32 - 8),
      then it must have size 0\<close>
lemma nodeValid_edge_of_addr_space:
  assumes "nodeValid s node"
  shows "(node +\<^sub>p 1) > node \<or> (node_size_masked s node) = 0"
  unfolding nodeValid_def
proof -
  have "unat (node_size_masked s node) * 8 < 2 ^ LENGTH(32)" using `nodeValid s node`
    unfolding nodeValid_def by meson
  hence "unat (node_size_masked s node) * 8 = unat ((node_size_masked s node) * 8)"
    using unat_mult_lem  by (metis eight_eq_eight)
  {assume "(node_size_masked s node) \<noteq> 0"    
    hence "(node_size_masked s node) * 8 \<noteq> 0"
      using `unat (node_size_masked s node) * 8 = unat ((node_size_masked s node) * 8)`
      using unat_eq_zero by fastforce
    hence "unat_ptr node + 8 < 2 ^ LENGTH(32)" 
      using `nodeValid s node` apply simp
      apply (frule nodeValid_node_node_size_upper_bound) 
      apply auto
      by (meson add_le_same_cancel1 le_def less_le_trans not_gr_zero unat_eq_zero) 
    hence "(node +\<^sub>p 1) > node" 
      unfolding ptr_add_def 
      apply (simp add:ptr_less_simp)
      by unat_arith auto
  } thus ?thesis by fast
qed
  
text \<open> if the footprint of a node, and the heap memory corresponding to the node 
      in two states are the same, and the node is valid in one state, 
      then it is valid in the other state as well \<close>  
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
    using intvl_upper_bound by auto
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
      using sable_isa.nodeValid_node_node_size_upper_bound2' apply blast
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
  
lemma nodesValid_trans_back: "nodeValid s node \<Longrightarrow> 
    nodesValid s (node_next s node) \<Longrightarrow>
    nodesValid s node"
  by(subst nodesValid_def', simp)
    
lemma nodesValid_reachable_imp_nodesValid: 
  "reachable s fst_node node \<Longrightarrow>
   nodesValid s fst_node \<Longrightarrow>  
   node \<noteq> NULL \<Longrightarrow> 
   nodesValid s node"
  apply (induction fst_node rule:nodesValid.induct)
    apply auto
   apply (metis sable_isa.nodesValid_def' sable_isa.reachable_helper3)
proof-
  fix s heap
  assume ih:"(reachable s (node_next s heap) node \<Longrightarrow> nodesValid s node)"
    and "reachable s heap node"
    and "nodesValid s (node_next s heap)"
    and "node \<noteq> NULL"
    and "nodeValid s heap"
    and "(node_next s heap) \<noteq> NULL"
  {
    assume "node = heap"
    have "nodesValid s heap" 
      using `nodesValid s (node_next s heap)` `nodeValid s heap`
      using nodesValid_trans_back by blast
    hence "nodesValid s node" using `node = heap` by auto
  }
  moreover {
    assume "node \<noteq> heap"
    have "heap \<noteq> NULL" using `nodeValid s heap` unfolding nodeValid_def Let_def
      using c_guard_NULL by blast
    have "node_next s heap > heap" using `nodeValid s heap` `(node_next s heap) \<noteq> NULL`
      unfolding nodeValid_def by meson
    with `reachable s heap node` `heap \<noteq> NULL` `(node_next s heap) \<noteq> NULL`  `node \<noteq> heap` 
    have "reachable s (node_next s heap) node"  
      using reachable.simps(4) by metis
    hence "nodesValid s node"
      using `node \<noteq> NULL` ih by blast   
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
  
  
lemma nodesValid_reachable_imp_nodeValid: 
  "nodesValid s heap_node \<Longrightarrow> 
   reachable s heap_node node \<Longrightarrow> 
   node \<noteq> NULL \<Longrightarrow> 
   nodeValid s node"
  apply (drule nodesValid_reachable_imp_nodesValid)
  by assumption+ (meson nodesValid_def')
    
lemma heaps_eq_nodesValid_reachable_imp_paths_eq_reachable[rule_format]:
  "(\<forall> p . p \<ge> ptr_val fst_node \<and> p < ptr_val to \<longrightarrow> hrs_the_same_at  s s' p) \<longrightarrow>
   nodesValid s fst_node \<longrightarrow>
   to \<noteq> NULL \<longrightarrow>
   reachable s fst_node to \<longrightarrow>
   path s fst_node to = path s' fst_node to \<and> reachable s' fst_node to" 
  apply (rule_tac ?a0.0=s and ?a1.0=fst_node and ?a2.0=to in  path.induct)    
   apply auto[1]
      apply (frule nodesValid_nodeValid)
      apply (frule reachable_helper1)
        apply auto[3]
      apply (rule path.simps(1)[THEN sym])
      apply auto[1]
     apply (rule_tac P="node = to" in split_goal)
      apply auto[1]
  using reachable_helper1 apply blast
    apply (rule_tac P="node = to" in split_goal)
     apply auto[1]
     apply (rule path.simps(1)[THEN sym])
     apply auto[1]
    apply clarify
    apply (frule reachable_next_le_to)
      apply auto[3]
   apply (metis (full_types) less_irrefl less_le_trans reachable.simps(2) reachable_next_le_to)
proof clarify    
  fix s node to
  assume ih:
    "(\<forall>p. ptr_val (node_next s node) \<le> p \<and> p < ptr_val to \<longrightarrow> hrs_the_same_at s s' p) \<longrightarrow>
       nodesValid s (node_next s node) \<longrightarrow>
       to \<noteq> NULL \<longrightarrow>
       reachable s (node_next s node) to \<longrightarrow>
       path s  (node_next s node) to = path s' (node_next s node) to \<and>
       reachable s' (node_next s node) to"
    and "node \<noteq> NULL"
    and "node < node_next s node"
    and "node_next s node \<le> to" 
    and heaps_eq:"\<forall>p. ptr_val node \<le> p \<and> p < ptr_val to \<longrightarrow> hrs_the_same_at s s' p"
    and "nodesValid s node" 
    and "to \<noteq> NULL"
    and "reachable s node to"
    
  have "node \<noteq> to" 
    using `node < node_next s node`[THEN ptr_less_simp[THEN iffD1]]
      `node_next s node \<le> to`[THEN ptr_le_simp[THEN iffD1]]
    by auto
  have "node_next s node \<noteq> NULL" using `node < node_next s node`[THEN ptr_less_simp[THEN iffD1]] 
    by auto
      
  have "(\<forall>p. ptr_val (node_next s node) \<le> p \<and> p < ptr_val to \<longrightarrow> hrs_the_same_at s s' p)"
    using `\<forall>p. ptr_val node \<le> p \<and> p < ptr_val to \<longrightarrow> hrs_the_same_at s s' p`
      `node < node_next s node`[THEN ptr_less_simp[THEN iffD1]]
    by force
  moreover have "nodesValid s (node_next s node)" 
    using `nodesValid s node` `node_next s node \<noteq> NULL`
    using nodesValid_not_next_null by blast
  moreover have "reachable s (node_next s node) to"
    using `reachable s node to` `node \<noteq> NULL` `node_next s node > node` `node \<noteq> to`
    using reachable.simps(4) by blast
  ultimately have "path s (node_next s node) to = path s' (node_next s node) to
    \<and> reachable s' (node_next s node) to"
    using `to \<noteq> NULL` ih by fast
  hence path_next_eq : "path s (node_next s node) to = path s' (node_next s node) to"
    and  "reachable s' (node_next s node) to"
    by blast+
      
  have "nodeValid s node" using `nodesValid s node`
      nodesValid_nodeValid by blast  
  have "0 \<notin> ptr_span node" using `nodeValid s node`
    unfolding nodeValid_def Let_def c_guard_def c_null_guard_def by blast
  have "unat_ptr node + 8 \<le> unat_ptr (node_next s node)" 
    using `nodeValid s node` `(node_next s node) \<noteq> NULL`
    unfolding nodeValid_def Let_def by simp  
  hence "unat_ptr node + 8 \<le> unat_ptr to"
    using `to \<ge> node_next s node`
    apply (simp add: ptr_le_simp) by unat_arith
  hence "\<forall>p \<in> ptr_span node. hrs_the_same_at s s' p"
    using heaps_eq intvl_upper_bound
      `0 \<notin> ptr_span node`  zero_not_in_intvl_lower_bound
    by (metis (mono_tags) less_le_trans mem_node_C_size word_less_nat_alt)
  hence "node_val s node = node_val s' node"
    using hrs_the_same_nodes_the_same by fast
  have "node_next s node = node_next s' node" 
    using `node_val s node = node_val s' node` by argo
  hence "node_next s' node \<le> to" and "node < node_next s' node"
    using `node_next s node \<le> to` `node < node_next s node` by argo+
      
  have 1:"path s node to = node # (path s (node_next s node) to)"
    using `node_next s node \<le> to` `node < node_next s node` \<open>node \<noteq> NULL\<close>
    using sable_isa.path.simps(2) by blast
  have 2:"path s' node to = node # (path s' (node_next s' node) to)"
    using `node_next s' node \<le> to` `node < node_next s' node` \<open>node \<noteq> NULL\<close>
    using sable_isa.path.simps(2) by blast
      
  have "path s (node_next s node) to = path s' (node_next s' node) to"
    using path_next_eq `node_next s node = node_next s' node` by argo
  hence "path s node to = path s' node to"
    using 1 2 by argo
  have "reachable s' (node_next s' node) to"
    using `reachable s' (node_next s node) to` `node_next s node = node_next s' node`
    by argo
  hence "reachable s' node to"
    using  `node \<noteq> NULL` `node \<noteq> to` `node < node_next s' node`
    using reachable.simps(4) by blast
  with `path s node to = path s' node to`
  show "path s node to = path s' node to \<and> reachable s' node to"  
    by argo
qed
  
lemma heaps_eq_nodesValid_reachable_imp_paths_eq[rule_format]:
  "(\<forall> p . p \<ge> ptr_val fst_node \<and> p < ptr_val to \<longrightarrow> hrs_the_same_at  s s' p) \<Longrightarrow>
   nodesValid s fst_node \<Longrightarrow>
   to \<noteq> NULL \<Longrightarrow>
   reachable s fst_node to \<Longrightarrow>
   path s fst_node to = path s' fst_node to" 
  using heaps_eq_nodesValid_reachable_imp_paths_eq_reachable by presburger
    
lemma heaps_eq_nodesValid_reachable_imp_reachable:
  "reachable s node to \<Longrightarrow>
    nodesValid s node \<Longrightarrow>
    \<forall>p . p \<ge> ptr_val node \<and> p < ptr_val to \<longrightarrow> hrs_the_same_at s s' p \<Longrightarrow>
    to \<noteq> NULL \<Longrightarrow>
    reachable s' node to" 
  using heaps_eq_nodesValid_reachable_imp_paths_eq_reachable by presburger 
    
lemma l11:"((x::word32) || (scast (y::  32 signed word))) && (scast (~~y)) = x && (scast (~~y))"
  apply (subst word_ao_dist)
proof -
  have " ((scast y)::word32) && scast (~~ y) = 0"
    apply (subst scast_NOT_simp)
    by auto
  hence " x && scast (~~ y) || scast y && scast (~~ y) = x && scast (~~ y) || 0"
    by (simp add: \<open>scast y && scast (~~ y) = 0\<close>)
  thus "x && scast (~~ y) || scast y && scast (~~ y) = x && scast (~~ y)"  by simp
qed
  
lemma mask_sw32_eq_0_eq_x :
  assumes "(x::word32) && scast (flag:: 32 signed word) = 0"
  shows " x && scast (~~flag) = x"
proof -
  have l1[simp]: "(scast (~~flag) :: word32) = ~~ ((scast flag)::word32)"
    using scast_NOT_simp by auto
  thus ?thesis using assms by (simp add: mask_eq_0_eq_x)
qed
  
text \<open>If a node n is in the path of another node fst_node, and nodesValid holds
      for fst_node, then n must be a valid node \<close>
lemma node_in_path_nodesValid_imp_nodeValid_node[rule_format]:
  "n \<in> set (path s fst_node to) \<longrightarrow> 
   nodesValid s fst_node \<longrightarrow>
   nodeValid s n" 
  apply (rule_tac ?a0.0=s and ?a1.0=fst_node and ?a2.0= to in path.induct)
   apply auto 
    apply (erule nodesValid_nodeValid)+
  apply (frule nodesValid_not_next_null)
  by auto
    
text \<open> if there is a node 'to' reachable from node 'node', then 'node' must be in its
      path to 'to', in other words, its path is not empty\<close>
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
    using unat_mult_lem  by (metis eight_eq_eight)
  have 0:"unat_ptr (node +\<^sub>p 1) + unat (?node_size * 8) \<le>  2 ^ LENGTH(32)"
    using `nodeValid s node` by (rule nodeValid_node_node_size_upper_bound')      
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
  
text \<open>if nodesValid holds for 'node', and all the nodes in the path from
      'heap' to 'node' are valid, then nodesValid holds for 'heap'\<close>
lemma path_nodeValid_reachable_imp_nodesValid[rule_format]:
  "nodeValid s heap_node \<longrightarrow>
   (\<forall> p \<in> set (path s heap_node node). nodeValid s p) \<longrightarrow>
   reachable s heap_node node \<longrightarrow>
   nodesValid s node \<longrightarrow>
   nodesValid s heap_node"
  apply (rule_tac ?a0.0=s and ?a1.0=heap_node and ?a2.0=node in path.induct) 
   apply (unfold nodeValid_def)[1] unfolding Let_def
   apply clarify
   apply (drule c_guard_NULL)
   apply auto[1]
        apply (metis sable_isa.nodesValid_not_null sable_isa.reachable_helper1)
       apply (metis reachable_helper1 sable_isa.nodesValid_not_null)
  using reachable_helper3 apply blast
     apply (metis dual_order.strict_iff_order order_less_le_trans nodesValid_not_null
      reachable.simps(4) reachable_helper2)
  using reachable_helper3 apply blast
   apply (metis dual_order.strict_iff_order order_less_le_trans reachable_helper2
      nodesValid_not_null reachable.simps(4))   
  apply auto
   apply (frule node_reachable_in_path)
     apply auto
   apply (frule nodesValid_not_null, auto)
  using sable_isa.nodesValid_def' unfolding Let_def by blast
    
lemma nodeValid_next_val: "nodeValid s node \<Longrightarrow>
  node_next s node \<noteq> NULL \<Longrightarrow>
  unat_ptr (node_next s node) \<ge> unat_ptr node + 8 +  unat ((node_size_masked s node) * 8)"
  unfolding nodeValid_def Let_def 
  by(simp split:if_split) 
    
lemma nodesValid_heaps_eq_nodeValid_in_path: 
  assumes "nodesValid s heap_node"
    and hrs_the_same: "\<forall> p . p \<ge> ptr_val heap_node \<and> p < ptr_val to \<longrightarrow> hrs_the_same_at s s' p"
    and "reachable s heap_node to"
    and "to \<noteq> NULL"
  shows "\<forall> n \<in> set (path s' heap_node to). nodeValid s' n"
proof-  
  have "path s heap_node to = path s' heap_node to"
    using hrs_the_same `nodesValid s heap_node` `reachable s heap_node to` `to \<noteq> NULL`
    using heaps_eq_nodesValid_reachable_imp_paths_eq  by blast
  { fix n
    assume n_in_path_s':"n \<in> set (path s' heap_node to)"    
    hence n_in_path:"n \<in> set (path s heap_node to)" using `path s heap_node to = path s' heap_node to`
      by argo
    have "n \<ge> heap_node" using n_in_path 
      using p_in_path_ge_node by blast
    have "nodeValid s n" using n_in_path `nodesValid s heap_node` 
      using node_in_path_nodesValid_imp_nodeValid_node by blast
    have c1:"\<forall> p . p\<ge> ptr_val n \<longrightarrow> p \<ge> ptr_val heap_node" using `n \<ge> heap_node` 
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
      by (metis \<open>nodeValid s n\<close> nodeValid_def eight_eq_eight unat_of_nat_eq word_arith_nat_mult)
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
  
lemma OCC_FLG_neg : "(scast (~~ MEM_NODE_OCCUPIED_FLAG) ::32 word) = ~~ scast MEM_NODE_OCCUPIED_FLAG"
  by (metis (no_types) mask_eq_0_eq_x l11 mask_sw32_eq_0_eq_x word_bw_comms(1) word_log_esimps(7) 
      word_log_esimps(9) word_not_not)    
 

    
text \<open>This lemma states that alloc() preserves the invariants. As the size of this proof
      suggests, most of the verification effort of alloc() was spent proving this lemma. \<close>    
lemma alloc'_invs:
  fixes size_bytes:: "32 word" and heap:: "unit ptr"
  assumes size_bytes_g0 : "size_bytes > 0"
  shows "\<lbrace>\<lambda>s. heap_invs s heap \<rbrace> (alloc' heap size_bytes) \<lbrace> \<lambda>r s. heap_invs s heap \<rbrace>"
  unfolding alloc'_def Let_def 
  apply (simp add: h_val_field_from_bytes)
    
  text \<open>We are introducing all the loop invariants in this command. By introducing the lemmas,
        'wp' will process the loop, and keeps the invariants as preconditions after the loop is done.
         \<close>
  apply (subst whileLoop_add_inv 
      [where I="\<lambda> (n,r) s. heap_invs s heap \<and>
                           reachable s (ptr_coerce heap) n \<and> 
                           (r=0 \<longrightarrow> (n = NULL \<or> ((size_bytes >> 3) + 1 \<le> node_size_masked s n) \<and> 
                           node_is_occupied s n = 0))" 
        and M="\<lambda> ((n,y),s). ptr_val n"])
  apply (wp)
      prefer 5
      apply assumption
     prefer 4
     apply (simp add: size_bytes_g0)
     apply (rule return_wp) 
  unfolding heap_invs_def
    apply (auto)    
  text \<open>Applying auto breaks the proof into multiple subgoals, all of which except two are
        trivially discharged. We discharge the trivial ones here, and leave the two main 
        subgoals for later.\<close>  
    
            prefer 11
            apply (wp, auto)
           apply(drule c_guard_NULL, drule nodesValid_reachable_imp_next_reachable, 
                 solves auto, solves auto, solves auto)+
    
  text \<open>This subgoal corresponds to the case where a free slot in the heap of exactly the 
      right size has been found \<close>
proof -
  fix a::"mem_node_C ptr"
  fix s::globals
  assume invs: "nodesValid s (ptr_coerce heap)"
    and node_free :"node_size s a && scast OCC_FLG = 0"
    and reachable: "reachable s (ptr_coerce heap) a"
    and "a \<noteq> NULL"
    and "c_guard a"
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
      
  have next_eq:"node_next ?new_s a = node_next s a" using updated_node_next by fast
      
  have hrs_the_same_except_a:"\<forall>p. p \<notin> ptr_span a \<longrightarrow> hrs_the_same_at s ?new_s p"
    using updated_node_hrs_the_same_elsewhere by blast   
  {
    assume "node_next s a = NULL"
    hence "node_next ?new_s a = NULL" using next_eq by presburger
    hence "nodesValid ?new_s a" using `nodeValid ?new_s a` by simp
  } moreover 
  {
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
      apply clarify
      apply(subgoal_tac "unat_ptr a + 8 \<le> unat p")
      by auto unat_arith
        
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
    using hrs_the_same_heap_to_a `reachable s ?heap_node a` `a \<noteq> NULL` `nodesValid s ?heap_node` 
    using heaps_eq_nodesValid_reachable_imp_reachable by blast
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
  text \<open>This subgoal corresponds to the case where the found slot in the heap is bigger than
      the requested size, and so a new free node must be created at the end of the allocated memory
      for the extra free space.\<close>
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
  have "?new_next \<noteq> NULL" using `c_guard ?new_next` c_guard_NULL by auto
  have "nodeValid s a" using nodesValid `reachable s (ptr_coerce heap) a` `a \<noteq> NULL`
    using nodesValid_reachable_imp_nodeValid by blast 
  have new_s_simp[simp]: "?new_s = ?new_s_real" by simp
  have new_size[simp]: "node_size ?new_s a= ?new_size " by (metis updated_node_size)
  have new_next[simp]: "node_next ?new_s a= ?new_next " by (metis updated_node_next)
      
  have "?next \<noteq> NULL \<longrightarrow> ?next > a" using `nodeValid s a` nodeValid_def by meson
      
      
  have "\<forall>p \<in> ptr_span a. unat p < unat_ptr a + 8"
    using intvl_upper_bound by auto
      
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
  have "unat ?node_size_masked * 8 < 2 ^ LENGTH(32)" 
    using `nodeValid s a` unfolding nodeValid_def by meson
  have node_size_masked_l_2p32:"(unat ?node_size_masked) * unat (8::32 word) < 2 ^ LENGTH(32)" 
    using `nodeValid s a` unfolding nodeValid_def apply(subst eight_eq_eight) by metis
  hence "((size_bytes >> 3) + 1) * 8 < ?node_size_masked * 8"
    using `(size_bytes >> 3) + 1  < ?node_size_masked`
    by (metis eight_eq_eight unat_0 word_gt_0_no word_mult_less_mono1 zero_neq_numeral)          
  moreover have "unat_ptr a + 8 + unat (?node_size_masked * 8) \<le> 2 ^ LENGTH(32)"
    using `nodeValid s a` nodeValid_node_node_size_upper_bound by fast 
  ultimately have "unat_ptr a + 8 + unat ( ((size_bytes >>3) +1) * 8) <  2 ^ LENGTH(32)"
    using `(size_bytes >>3) +1 < ?node_size_masked` `unat ?node_size_masked * 8 < 2 ^ LENGTH(32)`
    by unat_arith
      
  have "unat_ptr a + 8 + unat (((size_bytes >> 3) + 1) * 8) =
        unat (ptr_val a + 8 + ((size_bytes >> 3) + 1) * 8)"
    apply(insert `unat_ptr a + 8 + unat (((size_bytes >> 3) + 1) * 8) < 2 ^ LENGTH(32)`) 
    using  unat_add_lem_3
    by (metis eight_eq_eight) 
  hence "unat_ptr a + 8 + unat (?new_size_masked * 8) = unat_ptr (a +\<^sub>p uint (?new_size_masked + 1))"
    apply (simp only: new_size_eq)
    unfolding ptr_add_def apply (simp only: mem_node_C_size)
    unfolding ptr_val_def apply (simp only: of_int_uint)
    apply (subst (2) Rings.comm_semiring_class.distrib)
    by auto 
  hence "unat_ptr a + 8 + unat (((size_bytes >> 3) + 1) * 8) = unat_ptr ?new_next" 
    using new_size_eq by auto    
      
  have "\<forall>p \<in> ptr_span ?new_next. unat p \<ge> unat_ptr ?new_next"
    using `c_guard ?new_next` unfolding c_guard_def c_null_guard_def
    apply clarify
    apply (rule word_le_nat_alt[THEN iffD1])
    using zero_not_in_intvl_lower_bound by blast
  moreover have "\<forall>p \<in> ptr_span a. unat p < unat_ptr ?new_next"
    apply (subst `unat_ptr a + 8 + unat (((size_bytes >> 3) + 1) * 8) = unat_ptr ?new_next`[THEN sym])
    using `\<forall>p \<in> ptr_span a. unat p < unat_ptr a + 8`
    by auto
  ultimately have " ptr_span ?new_next \<inter> ptr_span a = {}" 
    by fastforce
  hence "node_val ?new_s ?new_next = mem_node_C ?new_next_size ?next" 
    apply (auto simp add: h_val_heap_update hrs_mem_update)
    apply (insert `ptr_span ?new_next \<inter> ptr_span a = {}`)
    apply (drule_tac h="hrs_mem (t_hrs_' (update_node s ?new_next (mem_node_C ?new_next_size ?next)))"
        in h_val_heap_update_disjoint)
    by (auto simp add: h_val_heap_update hrs_mem_update)
  hence "?next = node_next ?new_s ?new_next" by simp
  have "?new_next_size = node_size_masked ?new_s ?new_next "
    using `node_val ?new_s ?new_next = mem_node_C ?new_next_size ?next` by fastforce 
  have "unat ((size_bytes >> 3) + 1) * 8 < 2 ^ LENGTH(32)"
    apply (subgoal_tac "unat ?node_size_masked * 8 < 2 ^ LENGTH(32)")
    using `(size_bytes >> 3) + 1 < ?node_size_masked` 
     apply unat_arith
    using `nodeValid s a` unfolding nodeValid_def by meson
  have "unat ?node_size_masked * 8 < 2 ^ LENGTH(32)"
    using `nodeValid s a` unfolding nodeValid_def by meson 
  hence "unat (((size_bytes >> 3) + 1) * 8) = unat ((size_bytes >> 3) + 1) * 8"
    using \<open>unat ((size_bytes >> 3) + 1) * 8 < 2 ^ LENGTH(32)\<close>
    by (metis  eight_eq_eight unat_of_nat_eq word_arith_nat_mult)
  have "unat (?node_size_masked * 8) = unat ?node_size_masked * 8"
    using `unat ?node_size_masked * 8 < 2 ^ LENGTH(32)`
    by (metis  eight_eq_eight unat_of_nat_eq word_arith_nat_mult)   
      
  {
    assume "?next \<noteq> NULL"
    hence "?next > a" using `?next \<noteq> NULL \<longrightarrow> ?next > a` by fast
        
    have "unat ?node_size_masked * 8 = unat (?node_size_masked * 8)"
      using \<open>nodeValid s a\<close> unfolding nodeValid_def Let_def
      by (metis eight_eq_eight unat_of_nat_eq word_arith_nat_mult)    
    have 1:"unat_ptr a + 8 + unat ?node_size_masked * 8 \<le> unat_ptr ?next" 
      using `nodeValid s a` `?next \<noteq> NULL` unfolding nodeValid_def Let_def
      apply (subst `unat ?node_size_masked * 8 = unat (?node_size_masked * 8)`)
      by presburger
        
    have "unat ((size_bytes >> 3) + 1) * 8 = unat (((size_bytes >> 3) + 1) * 8)"
      using `unat ((size_bytes >> 3) + 1) * 8 < 2 ^ LENGTH(32)`
      by (metis eight_eq_eight unat_of_nat_eq word_arith_nat_mult)
        
    have 2:"unat_ptr a + 8 + unat ((size_bytes >> 3) + 1) * 8 = unat_ptr ?new_next"
      apply (insert `unat_ptr a + 8 + unat (((size_bytes >> 3) + 1) * 8) = unat_ptr ?new_next`)
      by(subst `unat ((size_bytes >> 3) + 1) * 8 = unat (((size_bytes >> 3) + 1) * 8)`)
        
    from `(size_bytes >> 3) + 1  < ?node_size_masked`
    have "unat ((size_bytes >> 3) + 1) * 8 + 8 \<le> unat ?node_size_masked * 8" by unat_arith
    hence "unat_ptr ?next \<ge> unat_ptr ?new_next + 8" 
      using 1 2 by unat_arith
  } note new_next_next_unat_rel = this
  {
    assume "?next \<noteq> NULL"
    hence "unat_ptr ?next \<ge> unat_ptr ?new_next + 8"
      using new_next_next_unat_rel by simp
    hence "unat_ptr ?next > unat_ptr ?new_next"
      using new_next_next_unat_rel by arith
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
    assume "?next \<noteq> NULL"
    hence "?next > ?new_next \<and> ?next \<ge> ?new_next +\<^sub>p 1"
      using next_new_next_rel by blast
    let ?halfway_s = "(update_node s ?new_next (mem_node_C ?new_next_size ?next))"
    let ?new_s = "(update_node ?halfway_s a (mem_node_C ?new_size ?new_next))"
    have "unat_ptr ?next \<ge> unat_ptr a + SZ_mem_node"
      using `nodeValid s a` `?next \<noteq> NULL` unfolding nodeValid_def Let_def
      by auto
    have "\<forall>p \<in> ptr_span ?new_next. unat p < unat_ptr ?new_next + 8"
      using intvl_upper_bound by auto
    have "unat_ptr ?next \<ge> unat_ptr ?new_next + SZ_mem_node"
      using `?next \<noteq> NULL` new_next_next_unat_rel by fastforce
    have "\<forall>p \<ge> ptr_val ?next. p \<notin> ptr_span ?new_next" 
      using `unat_ptr ?next \<ge> unat_ptr ?new_next + SZ_mem_node`
      using `\<forall>p \<in> ptr_span ?new_next. unat p < unat_ptr ?new_next + 8`
      apply auto
      apply (subgoal_tac "unat p \<ge>unat_ptr ?new_next + 8")
      by auto unat_arith    
    hence 1:"\<forall>p \<ge> ptr_val ?next. hrs_the_same_at s ?halfway_s p"  
      using updated_node_hrs_the_same_elsewhere by blast        
        
    have "\<forall>p \<ge> ptr_val ?next. p \<notin> ptr_span a" 
      using `unat_ptr ?next \<ge> unat_ptr a + SZ_mem_node`
      using `\<forall>p \<in> ptr_span a. unat p < unat_ptr a + 8`
      apply auto
      apply (subgoal_tac "unat p \<ge>unat_ptr a + 8")
      by auto unat_arith      
        
    hence 2:"\<forall>p \<ge> ptr_val ?next. hrs_the_same_at ?halfway_s ?new_s p"
      using updated_node_hrs_the_same_elsewhere by blast
        
    have "(\<forall>p \<ge> ptr_val ?next. hrs_the_same_at s ?new_s p)"
      using 1 2 by presburger
  } hence "?next \<noteq> NULL \<longrightarrow> (\<forall>p \<ge> ptr_val ?next. hrs_the_same_at s ?new_s p)" by blast
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
      using `nodeValid s a` nodeValid_node_size_upper_bound by blast
    have node_node_size_bound: "unat (ptr_val a) + 8 + unat (?node_size_masked * 8) 
      \<le> (if ?next \<noteq> NULL then unat (ptr_val ?next) else 2 ^ LENGTH(32))" 
      using `nodeValid s a` unfolding nodeValid_def Let_def by simp 
    have node_node_size_bound_weak:"unat (ptr_val a)+ 8+ unat (?node_size_masked* 8) \<le> 2^ LENGTH(32)" 
      using \<open>nodeValid s a\<close> sable_isa.nodeValid_node_node_size_upper_bound by blast
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
       apply (subgoal_tac "unat(8 +((size_bytes >>3) +1) *8) \<le> unat 8 +unat(((size_bytes >>3) +1) *8)")
        prefer 2
      using unat_add_le apply blast 
    proof - (* sledgehammered *)
      have f1: "\<And>w. unat (8 + (w::32 word)) \<le> 8 + unat w"
        by (metis eight_eq_eight unat_add_le)
      then have "\<And>w. unat (8 + (w::32 word)) \<le> 8 + 2 ^ len_of (TYPE(32)::32 itself)"
        by (meson add_le_cancel_left le_trans nat_less_le unat_lt2p)
      then have "\<And>n w. n \<le> 8 + 2 ^ len_of (TYPE(32)::32 itself) \<or> \<not> n \<le> unat (8 + (w::32 word))"
        using le_trans by blast
      then show "unat (8 + ((size_bytes >> 3) + 1) * 8) \<le> 8 + unat ((size_bytes >> 3) + 1) * 8"
        using f1 
        by (metis add_le_cancel_left nat_le_linear nat_less_le eight_eq_eight unat_mult_lem)
    next 
      have f1: "\<And>w wa. nat (uint (w::32 word)) < nat (uint wa) \<or> \<not> w < wa"
        by (simp add: unat_def word_less_nat_alt)
      have "1 + (size_bytes >> 3) < scast (~~ OCC_FLG) && node_size s a"
        by (metis \<open>(size_bytes >> 3) + 1 < node_size_masked s a\<close> add.commute word_bw_comms(1))
      then have "8 + 8 * nat (uint (1 + (size_bytes >> 3))) < 
                 8 + 8 * nat (uint (scast (~~ OCC_FLG) && node_size s a))"
        using f1 by auto
      thus "8 + unat ((size_bytes >> 3) + 1) * 8 < 8 + unat (node_size_masked s a) * 8"
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
           (if node_next ?new_s ?new_next \<noteq> NULL then unat_ptr (node_next ?new_s ?new_next) 
            else 2 ^ LENGTH(32))"
      using `?next = node_next ?new_s ?new_next` by presburger
        
    have "nodeFree s a" 
      using `node_size s a && scast OCC_FLG = 0` `nodeValid s a`
      unfolding nodeValid_def by meson
    have "?new_next_size = (?node_size_masked - (2 + (size_bytes >> 3)))"
      using \<open>?node_size_masked - (2 + (size_bytes >> 3)) && scast (~~ OCC_FLG) =
                 ?node_size_masked - (2 + (size_bytes >> 3))\<close> by blast 
    have "?new_next_size < ?node_size_masked"
      apply (subst `?new_next_size = (?node_size_masked - (2 + (size_bytes >> 3)))`)
      using `?node_size_masked > (size_bytes >> 3) + 1`
      by unat_arith
    hence "unat (node_size_masked ?new_s ?new_next) * 8 < 2 ^ LENGTH(32)"  
      apply (subst `?new_next_size =  (node_size_masked ?new_s ?new_next)`[THEN sym])
      using `unat ?node_size_masked * 8 < 2 ^ LENGTH(32)`
      by (simp add: nat_less_le word_less_nat_alt)
    have "nodeFree ?new_s ?new_next"
      unfolding nodeFree_def Let_def     
    proof-
      have "unat (ptr_val ( a +\<^sub>p 1)) + unat ?node_size_masked * 8 \<le> 2 ^ LENGTH(32)"
        using `nodeValid s a` nodeValid_node_node_size_upper_bound2' by fast
      have "\<forall>p \<in> {ptr_val (a +\<^sub>p 1)..+unat ?node_size_masked * SZ_mem_node}.
              snd (hrs_htd (t_hrs_' s) p) = Map.empty" using `nodeFree s a` 
        by (simp add: sable_isa.nodeFree_def)
      with `unat (ptr_val ( a +\<^sub>p 1)) + unat ?node_size_masked * 8 \<le> 2 ^ LENGTH(32)`
      have 1:
        "\<forall>p. p\<ge> ptr_val(a +\<^sub>p 1) \<and> unat p < unat_ptr(a +\<^sub>p 1) +unat ?node_size_masked *SZ_mem_node \<longrightarrow>
                snd (hrs_htd (t_hrs_' s) p) = Map.empty"
        by (simp add: intvl_no_overflow2) 
          
      {assume "unat_ptr ?new_next + 8 \<ge> 2 ^ LENGTH(32)"
          
        have "unat_ptr a + 8 + unat (((size_bytes >> 3) + 1) * 8) + 8 \<le> 2 ^ LENGTH(32)"
          apply (insert `unat_ptr a + 8 + unat (?node_size_masked * 8) \<le> 2 ^ LENGTH(32)`)
          apply (subst `unat (((size_bytes >> 3) + 1) * 8) = unat ((size_bytes >> 3) + 1) * 8`)
          apply (subst (asm) `unat (?node_size_masked * 8) = unat ?node_size_masked * 8`)  
          using `((size_bytes >> 3) + 1) < ?node_size_masked `
          by unat_arith
        have "unat_ptr a + 8 + unat (((size_bytes >> 3) + 1) * 8) + 8 \<ge> 2 ^ LENGTH(32)"
          using `unat_ptr ?new_next + 8 \<ge> 2 ^ LENGTH(32)`
          apply (subst (asm)`unat_ptr a + 8 + unat(((size_bytes >> 3) + 1) * 8) =unat_ptr ?new_next`
              [THEN sym])
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
        have "?new_next > a"
          using `unat_ptr a + 8 + unat (((size_bytes >> 3) + 1) * 8) = unat_ptr ?new_next`
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
          apply (drule nodeValid_node_node_size_upper_bound2)
          using `(size_bytes >> 3) + 1  < ?node_size_masked` by unat_arith
        hence "unat_ptr (a +\<^sub>p 1) = unat_ptr a + 8" 
          unfolding ptr_add_def by unat_arith
            
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
          by (metis eight_eq_eight unat_mult_lem)
            
        have "unat_ptr ?new_next = unat_ptr a + unat (2 + (size_bytes >>3)) * 8"
          apply (subst `unat (2 + (size_bytes >>3)) = 1 + unat ((size_bytes >>3) + 1)`)
          apply (subst `unat_ptr a + 8 + unat (((size_bytes >> 3) + 1) * 8) = unat_ptr ?new_next`
              [THEN sym])
          apply (subst `unat (((size_bytes >> 3) + 1) * 8) = unat ((size_bytes >> 3) + 1) * 8`) 
          by auto 
            
        have "unat_ptr (?new_next +\<^sub>p 1) + unat ?new_next_size * SZ_mem_node
               = unat_ptr (a +\<^sub>p 1) + unat ?node_size_masked * SZ_mem_node" 
          apply (subst `unat_ptr (?new_next +\<^sub>p 1) = unat_ptr ?new_next + 8`)
          apply (subst `unat_ptr ?new_next = unat_ptr a + unat (2 + (size_bytes >>3)) * 8`)
          apply (subst `unat_ptr (a +\<^sub>p 1) = unat_ptr a + 8`)
          apply (subst `?new_next_size = (?node_size_masked - (2 + (size_bytes >> 3)))`)
          apply (subst `unat (?node_size_masked - (2 + (size_bytes >> 3))) = 
                         unat ?node_size_masked - unat (2 + (size_bytes >> 3))`)
          using `unat ?node_size_masked \<ge> unat (2 + (size_bytes >> 3))`
          by auto
            
        hence 3: "unat_ptr (?new_next +\<^sub>p 1) + unat (node_size_masked ?new_s ?new_next) * SZ_mem_node
                    = unat_ptr (a +\<^sub>p 1) + unat ?node_size_masked * SZ_mem_node" 
          using `?new_next_size = node_size_masked ?new_s ?new_next`
          by argo
            
        hence 4: 
          "unat_ptr (?new_next +\<^sub>p 1)+ (unat (node_size_masked ?new_s ?new_next))* SZ_mem_node \<le> 
           2 ^ LENGTH(32)"
          using \<open>nodeValid s a\<close> nodeValid_node_node_size_upper_bound2' by auto
        hence 
          "\<forall>p. p \<ge> ptr_val (?new_next +\<^sub>p 1) \<and> 
               unat p< unat_ptr(?new_next +\<^sub>p 1) +(unat (node_size_masked ?new_s ?new_next)) * SZ_mem_node \<longrightarrow> 
               p \<ge> ptr_val (a +\<^sub>p 1) \<and> unat p < unat_ptr (a +\<^sub>p 1) + unat ?node_size_masked * SZ_mem_node"
          using  2 3 by force
            
        hence "\<forall>p \<in> array_span (?new_next +\<^sub>p 1) (unat (node_size_masked ?new_s ?new_next)).
                p \<ge> ptr_val (a +\<^sub>p 1) \<and> unat p < unat_ptr (a +\<^sub>p 1) + unat ?node_size_masked * SZ_mem_node"
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
            (if node_next ?new_s ?new_next \<noteq> NULL then unat_ptr (node_next ?new_s ?new_next) 
             else 2 ^ LENGTH(32))`
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
      using `?next \<noteq> NULL`
      using `?next \<noteq> NULL \<longrightarrow> (\<forall>p \<ge> ptr_val ?next. hrs_the_same_at s ?new_s p)`
      by fast
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
    apply (rule dobule_update_heaps_eq_before) using new_next_g_a 
    using `c_guard a` `c_guard ?new_next` unfolding c_guard_def 
    by (auto simp:ptr_less_def' ptr_less_def)
  hence hrs_the_same_heap_to_a:
    "\<forall> p. p \<ge> ptr_val ?heap_node \<and> p < ptr_val a \<longrightarrow> hrs_the_same_at s ?new_s p"
    by simp  
  hence paths_the_same:"path s ?heap_node a = path ?new_s ?heap_node a"
    using `reachable s ?heap_node a` `nodesValid s ?heap_node` `a \<noteq> NULL`
    using  heaps_eq_nodesValid_reachable_imp_paths_eq by blast     
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
      heaps_eq_nodesValid_reachable_imp_reachable by blast     
      
  {assume "a > ptr_coerce heap" 
    hence "a \<noteq> ptr_coerce heap" by simp
    hence "(ptr_coerce heap) \<in> set (path s (ptr_coerce heap) a)" 
      using `nodesValid s (ptr_coerce heap)` `reachable s (ptr_coerce heap) a` `a \<noteq> NULL` 
        node_reachable_in_path by fast
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
  
  
  
text \<open>a helper theorem for alloc'_hoare, it proves the main goals for alloc'_hoare after it 
      has gone through wp. The main goals correspond to the two branches of alloc(), one where
      a free portion of exactly the correct size has been found, another where a free portion
      bigger than the required size has been found. For the purposes of alloc'_hoare, the
      preconditions required for the two branches turn out to be the same \<close>
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
    using `nodeValid s node`  sable_isa.nodeValid_node_node_size_upper_bound' by presburger   
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
      apply (simp add: shiftr3_is_div_8) apply (rule word_div_mult_lower_bound)
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
  
text \<open>This is the main theorem. It proves that given the heap_invs precondition, if the returned 
      pointer is not NULL, it is of the correct size, it is properly aligned with respect to the type the memory 
      is being allocated for, and it points to a previously free (untyped) portion of the heap\<close>  
lemma alloc'_hoare:
  fixes size_bytes :: "32 word"
  assumes align: "align_of TYPE('a) dvd align_of TYPE(mem_node_C)"
    and n: "size_of TYPE('a) \<le> unat size_bytes" and "0 < size_bytes"
  shows "\<lbrace>\<lambda>s. heap_invs s heap_node\<rbrace> alloc' heap_node size_bytes
       \<lbrace>\<lambda>r s. let ptr = (ptr_coerce r) :: ('a :: mem_type) ptr in
        ptr_val r \<noteq> 0 \<longrightarrow> heap_ptr_valid (ptr_retyp ptr (hrs_htd (t_hrs_' s))) ptr\<rbrace>"
  unfolding alloc'_def Let_def 
  apply (simp add: h_val_field_from_bytes)
  apply (subst whileLoop_add_inv 
      [where I="\<lambda> (n,r) s. heap_invs s heap_node \<and> 
                           reachable s (ptr_coerce heap_node) n \<and> 
                           (r=0 \<longrightarrow> n = NULL \<or> ((size_bytes >> 3) + 1 \<le> node_size_masked s n) \<and> 
                           node_is_occupied s n = 0)" 
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
  unfolding heap_invs_def
           apply(drule nodesValid_reachable_imp_next_reachable, auto)
          apply(drule nodesValid_reachable_imp_next_reachable, auto)
         apply(drule nodesValid_reachable_imp_next_reachable, auto)
        apply(drule nodesValid_reachable_imp_next_reachable, auto)
       apply(drule nodesValid_reachable_imp_next_reachable, auto)
  apply(drule nodesValid_reachable_imp_next_reachable, auto)
  apply(drule nodesValid_reachable_imp_next_reachable, auto)
  apply(drule nodesValid_reachable_imp_next_reachable, auto)
    
  using n align apply (rule alloc'_hoare_helper, unfold heap_invs_def, auto)
  using n align apply (rule alloc'_hoare_helper, unfold heap_invs_def, auto) 
  done
    
    
    (* lemma alloc_w32_safe: "\<lbrace>\<lambda>s. (liftC lift_global_heap (\<lambda>s. heap_invs s heap)) s\<rbrace>
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
  oops *)
end
  
end
