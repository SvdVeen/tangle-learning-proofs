chapter \<open>Parity Games\<close>
theory ParityGames
imports Main
begin
section \<open>Parity Game Definitions\<close>
subsection \<open>Directed Graphs\<close>
text \<open>
  An arena \<A> in parity games consists of a directed graph and sets of vertices with owners.
  It is defined as \<A> = (V,V0,V1,E) where
  - (V,E) is a directed graph
  - V0 and V1 = V\V0 are sets of vertices belonging to the two players
  - E \<subseteq> V \<times> V is a set of edges, such that every vertex has at least one successor
  The simplest way for us to represent this is as a directed graph of integers (which will be priorities),
  and a set of vertices belonging to player 0.
\<close>
text \<open>A directed graph is represented as a set of edges\<close>
type_synonym 'v dgraph = "('v\<times>'v) set"
definition succs :: "'v dgraph \<Rightarrow> 'v \<Rightarrow> 'v set" where
  "succs E v \<equiv> E``{v}"
definition is_succ :: "'v dgraph \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> bool" where
  "is_succ E v w \<equiv> w \<in> succs E v"

lemma "w \<in> succs E v \<Longrightarrow> is_succ E v w"
  unfolding is_succ_def succs_def by auto

subsection \<open>Paths and Cycles\<close>
context
  fixes E :: "'v dgraph"
begin
  (*definition V where "V = fst`E \<union> snd`E"

  lemma "finite E \<Longrightarrow> finite V"
    unfolding V_def by simp
  *)

  (** A path consisting of the edges of a graph *)
  fun epath :: "'v \<Rightarrow> ('v\<times>'v) list \<Rightarrow> 'v \<Rightarrow> bool" where
    "epath v [] v' \<longleftrightarrow> v=v'"
  | "epath v ((x,y)#es) v' \<longleftrightarrow> x=v \<and> (x,y)\<in>E \<and> epath y es v'"

  (** A path consisting of the second node of each edge of a graph *)
  fun path :: "'v \<Rightarrow> 'v list \<Rightarrow> 'v \<Rightarrow> bool" where
     "path v [] v' \<longleftrightarrow> v = v'"
  |  "path v (x#xs) v' \<longleftrightarrow> (v,x) \<in> E \<and> path x xs v'"

  (** Quick check whether the path definition does in fact hold the second node of each edge *)
  lemma "path v vs v' \<Longrightarrow> vs \<noteq> [] \<Longrightarrow> v' \<in> set vs"
    apply (induction vs arbitrary: v) by fastforce+

  (** A path consisting of the first node of each edge of a graph  *)
  fun path' :: "'v \<Rightarrow> 'v list \<Rightarrow> 'v \<Rightarrow> bool" where
     "path' v [] v' \<longleftrightarrow> v = v'"
  |  "path' v (x#xs) v' \<longleftrightarrow> (\<exists>y. x=v \<and> (v,y) \<in> E \<and> path' y xs v')"

  lemma
    "path' v [] v' \<longleftrightarrow> v = v'"
    "path' v [x] v' \<longleftrightarrow> v = x \<and> (x,v') \<in> E"
    "path' v (x#(x'#xs)) v' \<longleftrightarrow> v = x \<and> (x,x') \<in> E \<and> path' x'(x'#xs) v'"
    by auto

  (** These lemmas show that the two path definitions are alternative definitions for the edge paths *)
  lemma path_alt: "path u xs v \<longleftrightarrow> (\<exists>es. epath u es v \<and> xs=map snd es)"
    apply (induction xs arbitrary: u)
    subgoal by auto
    subgoal for a xs u apply auto
      by (metis epath.simps(2) list.simps(9) snd_conv)
    done

  lemma path'_alt: "path' u xs v \<longleftrightarrow> (\<exists>es. epath u es v \<and> xs=map fst es)"
    apply (induction u xs v rule: path'.induct)
    apply (auto simp: Cons_eq_map_conv)
    using epath.simps(2) by blast+

  (** These lemmas show that the paths can be composed by appending multiple paths *)
  lemma epath_append[simp]: "epath u (es\<^sub>1@es\<^sub>2) v \<longleftrightarrow> (\<exists>u'. epath u es\<^sub>1 u' \<and> epath u' es\<^sub>2 v)"
    apply (induction es\<^sub>1 arbitrary: u) by auto

  lemma path_append[simp]: "path u (xs\<^sub>1@xs\<^sub>2) v \<longleftrightarrow> (\<exists>u'. path u xs\<^sub>1 u' \<and> path u' xs\<^sub>2 v)"
    apply (induction xs\<^sub>1 arbitrary: u) by auto

  lemma path'_append[simp]: "path' u (xs\<^sub>1@xs\<^sub>2) v \<longleftrightarrow> (\<exists>u'. path' u xs\<^sub>1 u' \<and> path' u' xs\<^sub>2 v)"
    apply (induction xs\<^sub>1 arbitrary: u) by auto

  (** These lemmas show that paths can be decomposed in various ways *)
  lemma path_decomp_1: "path u (xs@[v]@ys) w \<Longrightarrow> path u (xs@[v]) v" by auto

  lemma path_decomp_2: "path u (xs@[v]@ys@[w]@zs) x \<Longrightarrow> path v (ys@[w]) w" by auto

  lemma path'_decomp_1: "path' u (xs@[v]@ys) w \<Longrightarrow> path' u (xs) v" by auto

  lemma path'_decomp_2: "path' u (xs@[v]@ys@[w]@zs) x \<Longrightarrow> path' v (v#ys) w" by auto

  (** These lemmas show that paths are equivalent to the reflexive transitive closure *)
  lemma epath_is_rtrancl: "epath v es v' \<Longrightarrow> (v,v')\<in>E\<^sup>*"
  proof (induction es v' rule: epath.induct)
    case (1 v v') thus ?case by simp
  next
    case (2 v x y es v')
    hence "(v,y) \<in> E" by auto
    with 2 show ?case by simp
  qed

  lemma rtrancl_is_epath: "(v,v')\<in>E\<^sup>* \<Longrightarrow> \<exists>es. epath v es v'"
    apply (induction rule: converse_rtrancl_induct)
    using epath.simps(1) epath.simps(2) by blast+

  lemma epath_equiv_rtrancl: "(u,v)\<in>E\<^sup>* \<longleftrightarrow> (\<exists>es. epath u es v)"
    apply auto by (simp add: rtrancl_is_epath epath_is_rtrancl)+

  lemma path_is_rtrancl: "path v xs v' \<Longrightarrow> (v,v')\<in>E\<^sup>*"
    apply (induction xs arbitrary: v) by fastforce+

  lemma rtrancl_is_path: "(v,v')\<in>E\<^sup>* \<Longrightarrow> \<exists>xs. path v xs v'"
    apply (induction rule: converse_rtrancl_induct)
    using path.simps(1) path.simps(2) by blast+

  lemma path_equiv_rtrancl: "(v,v') \<in> E\<^sup>* \<longleftrightarrow> (\<exists>xs. path v xs v')"
    apply auto by (simp add: rtrancl_is_path path_is_rtrancl)+

  lemma path'_is_rtrancl: "path' v xs v' \<Longrightarrow> (v,v')\<in>E\<^sup>*"
    apply (induction xs arbitrary: v) by fastforce+

  lemma rtrancl_is_path': "(v,v')\<in>E\<^sup>* \<Longrightarrow> \<exists>xs. path' v xs v'"
    apply (induction rule: converse_rtrancl_induct)
    using path'.simps(1) path'.simps(2) by blast+

  lemma path'_equiv_rtrancl: "(v,v') \<in> E\<^sup>* \<longleftrightarrow> (\<exists>xs. path' v xs v')"
    apply auto by (simp add: rtrancl_is_path' path'_is_rtrancl)+

  (** These lemmas show that paths are a subset of the graph *)
  lemma epath_subset: "epath v es v' \<Longrightarrow> set es \<subseteq> E"
    using split_list by fastforce

  lemma path_subset: "path v xs v' \<Longrightarrow> set xs \<subseteq> fst`E \<union> snd`E"
  proof (induction xs arbitrary: v)
    case Nil
    then show ?case by simp
  next
    case (Cons a xs)
    hence "(v,a) \<in> E" by simp
    hence "a \<in> snd ` E" by force
    with Cons show ?case by auto
  qed

  lemma path'_subset: "path' v xs v' \<Longrightarrow> set xs \<subseteq> fst`E \<union> snd`E"
  proof (induction xs arbitrary: v)
    case Nil
    then show ?case by simp
  next
    case (Cons a xs)
    hence "v = a" by auto
    moreover from this Cons have "\<exists>y. (v,y)\<in>E" by auto
    ultimately have "a \<in> fst ` E" by force
    with Cons show ?case by auto
  qed

  lemma path_equiv_path': "path v (xs@[v']) v' \<Longrightarrow> path' v (v#xs) v'"
    apply (induction xs arbitrary: v) by auto

  lemma path'_equiv_path: "path' v (v#xs) v' \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> path v (xs@[v']) v'"
    apply (induction xs arbitrary: v) by fastforce+

  lemma origin_in_path':  "path' v vs v' \<and> vs \<noteq> [] \<Longrightarrow> v \<in> set vs" by (cases vs) auto

  lemma path'D: "path' v vs v' \<and> vs \<noteq> [] \<Longrightarrow> \<exists>y vs'. vs = v#(vs') \<and> (v,y) \<in> E \<and> path' y vs' v'"
    apply (induction vs arbitrary: v) by simp+

  lemma path'_loop: "path' v (x#y#ys) v \<Longrightarrow> path' y (y#ys@[v]) y"
    by (induction ys arbitrary: v; simp)

  lemma distinct_length: "distinct xs \<Longrightarrow> length xs = card (set xs)"
    apply (induction xs) by auto

  lemma not_distinct_length: "length xs > card (set xs) \<Longrightarrow> \<not>distinct xs"
    apply (induction xs) by auto

  lemma finite_subset_not_distinct: "finite S \<Longrightarrow> set xs \<subseteq> S \<Longrightarrow> length xs > card S \<Longrightarrow> \<not>distinct xs"
  proof (rule ccontr; simp)
    assume finite: "finite S"
      and subset: "set xs \<subseteq> S"
      and len: "length xs > card S"
      and distinct: "distinct xs"
    hence "card (set xs) = length xs" by (simp add: distinct_length)
    with len have card_gt: "card (set xs) > card S" by simp
    also from subset finite have card_lt_eq: "card (set xs) \<le> card S"
      using card_mono by blast
    finally show "False" by auto
  qed

  definition cycle_node :: "'v \<Rightarrow> 'v list \<Rightarrow> bool" where
    "cycle_node v xs \<equiv> path' v xs v \<and> xs \<noteq> []"

  lemma cycle_node_not_empty[simp]:"\<not>cycle_node v []"
    unfolding cycle_node_def by auto

  definition cycle_from_node :: "'v \<Rightarrow> 'v list \<Rightarrow> bool" where
    "cycle_from_node v xs \<equiv> \<exists>v'. (v,v')\<in>E\<^sup>* \<and> cycle_node v' xs"

  lemma cycle_from_node_not_empty[simp]: "\<not>cycle_from_node v []"
    unfolding cycle_from_node_def by auto

  lemma cycle_from_node_comp: "path' u xs v \<Longrightarrow> cycle_node v ys \<Longrightarrow> cycle_from_node u ys"
    unfolding cycle_from_node_def using path'_is_rtrancl by blast

  lemma cycle_from_node_decomp: "cycle_from_node u ys \<Longrightarrow> \<exists>xs v. cycle_node v ys \<and> path' u xs v"
    unfolding cycle_from_node_def using rtrancl_is_path' by blast

  definition lasso_from_node :: "'v \<Rightarrow> 'v list \<Rightarrow> 'v list \<Rightarrow> bool" where
    "lasso_from_node v xs ys \<equiv> \<exists>v'. path' v xs v' \<and> path' v' ys v' \<and> ys \<noteq> []"

  lemma lasso_from_node_not_empty[simp]:"\<not>lasso_from_node v xs []"
    unfolding lasso_from_node_def by auto

  lemma origin_in_lasso: "lasso_from_node x xs ys \<Longrightarrow> (x \<in> set xs \<or> x \<in> set ys)"
    unfolding lasso_from_node_def
    apply (induction xs arbitrary: x; simp)
    using origin_in_path' by auto

  definition lasso_from_node' :: "'v \<Rightarrow> 'v list \<Rightarrow> bool" where
    "lasso_from_node' v xs \<equiv> \<exists>v' xs1 xs2. xs=xs1@xs2 \<and>  path' v xs1 v' \<and> path' v' xs2 v' \<and> xs2 \<noteq> []"

  lemma lasso_from_node'_not_empty[simp]: "\<not>lasso_from_node' v []"
    unfolding lasso_from_node'_def by auto

  lemma lasso_from_node'_length: "lasso_from_node' v vs \<Longrightarrow> 0 < length vs"
    unfolding lasso_from_node'_def by fast

  lemma cycle_impl_lasso': "cycle_node v xs \<Longrightarrow> lasso_from_node' v xs"
    unfolding cycle_node_def lasso_from_node'_def by fastforce

  lemma lassos_equiv: "lasso_from_node' v xs \<longleftrightarrow> (\<exists>xs1 xs2. xs=xs1@xs2 \<and> lasso_from_node v xs1 xs2)"
    unfolding lasso_from_node'_def lasso_from_node_def
    apply (induction xs arbitrary: v) by auto

  lemma lasso'_impl_path: "lasso_from_node' v xs \<Longrightarrow> \<exists>v'. path' v xs v'"
    unfolding lasso_from_node'_def by force

  lemma origin_in_lasso': "lasso_from_node' v xs \<Longrightarrow> v \<in> set xs"
    apply (induction xs arbitrary: v; simp)
    using lasso'_impl_path origin_in_path' by fastforce

  lemma lasso'_iff_path: "lasso_from_node' v xs \<longleftrightarrow> (\<exists>v'\<in>set xs. path' v xs v')"
    unfolding lasso_from_node'_def
    apply (auto simp: in_set_conv_decomp neq_Nil_conv) by force

  lemma lasso_from_node'_consD: "lasso_from_node' v (x#xs)
    \<Longrightarrow> (\<exists>v' xs'. x=v \<and> (v,v')\<in>E \<and> lasso_from_node' v' xs' \<and> set xs'\<subseteq>set (x#xs))"
    by (auto simp: lasso_from_node'_def Cons_eq_append_conv; force)

  lemma lasso_from_node'_prepend: "\<lbrakk> lasso_from_node' v' xs; (v,v') \<in> E \<rbrakk> \<Longrightarrow> lasso_from_node' v (v#xs)"
    unfolding lasso_from_node'_def
    apply (induction xs arbitrary: v')
    subgoal by simp
    subgoal for x' xs' by (metis ParityGames.path'.simps(2) append_Cons)
    done

  lemma self_lasso': "\<lbrakk> path' v vs v; vs \<noteq> [] \<rbrakk> \<Longrightarrow> lasso_from_node' v vs"
    unfolding lasso_from_node'_def by force

  lemma lasso'_close_loop: "\<lbrakk> path' v' vs v; vs \<noteq> []; (v,v') \<in> E \<rbrakk> \<Longrightarrow> lasso_from_node' v' (vs@[v])"
    unfolding lasso_from_node'_def by fastforce

  lemma lasso'_extend_loop: "lasso_from_node' v vs \<Longrightarrow> \<exists>vs'. length vs < length vs' \<and> set vs = set vs' \<and> lasso_from_node' v vs'"
  proof -
    assume lasso: "lasso_from_node' v vs"
    then obtain v' vs1 vs2 where
      vs_decomp: "vs = vs1@vs2" and
      path_vs1: "path' v vs1 v'" and
      path_vs2: "path' v' vs2 v'" and
      vs2_not_empty: "vs2 \<noteq> []"
      unfolding lasso_from_node'_def by blast
    define vs' where "vs' = vs1@vs2@vs2"
    show ?thesis
    proof (rule exI[where x=vs']; intro conjI)
      from vs_decomp vs2_not_empty show "length vs < length vs'"
        unfolding vs'_def by fastforce
      from vs_decomp show "set vs = set vs'"
        unfolding vs'_def by simp
      from path_vs1 path_vs2 vs2_not_empty show "lasso_from_node' v vs'"
        unfolding lasso_from_node'_def vs'_def by fastforce
    qed
  qed

  lemma lasso'_extend_any_length: "lasso_from_node' v vs \<Longrightarrow> \<exists>vs'. n < length vs' \<and> set vs = set vs' \<and> lasso_from_node' v vs'"
    apply (induction n)
    subgoal using lasso_from_node'_length by blast
    subgoal using lasso'_extend_loop Suc_lessI by metis
    done

  lemma lasso_from_equiv_cycle_from: "cycle_from_node v ys \<longleftrightarrow> (\<exists>xs. lasso_from_node v xs ys)"
    unfolding lasso_from_node_def cycle_from_node_def cycle_node_def
  proof
    assume "\<exists>v'. (v,v') \<in> E\<^sup>* \<and> path' v' ys v' \<and> ys \<noteq> []"
    then show "\<exists>xs v'. local.path' v xs v' \<and> local.path' v' ys v' \<and> ys \<noteq> []"
      using path'_equiv_rtrancl by auto
  next
    assume "\<exists>xs v'. path' v xs v' \<and> path' v' ys v' \<and> ys \<noteq> []"
    then show "\<exists>v'. (v,v') \<in> E\<^sup>* \<and> path' v' ys v' \<and> ys \<noteq> []"
      using path'_is_rtrancl by auto
  qed
end

locale finite_graph_V =
  fixes E :: "'v dgraph"
  fixes V :: "'v set"
  assumes E_in_V: "E \<subseteq> V \<times> V"
  assumes fin_V[simp, intro]: "finite V"
  assumes succ: "v\<in>V \<Longrightarrow> E``{v}\<noteq>{}"
begin
  lemma fin_E[simp, intro!]: "finite E"
    using E_in_V by (simp add: finite_subset)

  lemma path_closed_V: "v\<in>V \<Longrightarrow> path' E v xs v' \<Longrightarrow> v'\<in>V"
    apply (induction xs arbitrary: v)
    using E_in_V
    by auto

  lemma path_any_length: "\<lbrakk>v\<in>V\<rbrakk> \<Longrightarrow> \<exists>xs v'. length xs = n \<and> path' E v xs v'"
  proof (induction n)
    case 0
    then obtain xs v' where "xs=([]::'v list)" and "v' = v" by simp
    then show ?case by auto
  next
    case (Suc n)
    then obtain xs v' where path: "length xs = n" "path' E v xs v'" by auto
    from path_closed_V[OF \<open>v\<in>V\<close> path(2)] Suc succ obtain w where succ: "w \<in> E``{v'}" by blast
    then obtain ys where append: "ys = xs@[v']" by fast
    with path have length: "length ys = Suc n" by simp
    from append path succ have "path' E v ys w" by auto
    with length show ?case by auto
  qed

  lemma finite_graph_always_has_cycle_from_node: "x\<in>V \<Longrightarrow> \<exists>xs. cycle_from_node E x xs"
  proof -
    assume "x\<in>V"
    then obtain xs x' where xs: "length (xs::'v list) = (card V) + 1 \<and> path' E x xs x'"
      using path_any_length by blast
    have "\<not>distinct xs" proof -
      from xs have "set xs \<subseteq> V" using path'_subset E_in_V by fastforce
      moreover from xs have "length xs > card V" by auto
      ultimately show ?thesis using finite_subset_not_distinct by blast
    qed
    hence "\<exists>y xs1 xs2 xs3. xs = xs1 @ [y] @ xs2 @ [y] @ xs3" using not_distinct_decomp by blast
    then obtain y xs1 xs2 xs3 where decomp: "xs = xs1 @ [y] @ xs2 @ [y] @ xs3" by blast
    with xs have "path' E x (xs1) y" by auto
    moreover from decomp xs have "path' E y (y#xs2) y" by auto
    hence "cycle_node E y (y#xs2)" by (simp add: cycle_node_def)
    ultimately have "cycle_from_node E x (y#xs2)" using cycle_from_node_comp by fastforce
    then show "\<exists>xs. cycle_from_node E x xs" by auto
  qed

  lemma finite_graph_always_has_lasso': "x\<in>V \<Longrightarrow> \<exists>xs. lasso_from_node' E x xs"
  proof-
    assume "x\<in>V"
    then obtain xs x' where xs: "length (xs::'v list) = (card V) + 1 \<and> path' E x xs x'"
      using path_any_length by blast
    have "\<not>distinct xs" proof -
      from xs have "set xs \<subseteq> V" using path'_subset E_in_V by fastforce
      moreover from xs have "length xs > card V" by auto
      ultimately show ?thesis using finite_subset_not_distinct by blast
    qed
    hence "\<exists>y xs1 xs2 xs3. xs = xs1 @ [y] @ xs2 @ [y] @ xs3" using not_distinct_decomp by blast
    then obtain y xs1 xs2 xs3 where decomp: "xs = xs1 @ [y] @ xs2 @ [y] @ xs3" by blast
    with xs have "path' E x xs1 y" by auto
    moreover from decomp xs have "path' E y (y#xs2) y" by auto
    ultimately have "lasso_from_node' E x (xs1@(y#xs2))" unfolding lasso_from_node'_def by blast
    then show "\<exists>xs. lasso_from_node' E x xs" by auto
  qed

end

subsection \<open>Paths in Subgraphs\<close>

lemma simulate_path_aux:
  assumes "E``(Y-X) \<subseteq> Y"
  assumes "v\<in>Y"
  assumes "path' E v xs v'"
  shows "X\<inter>set xs \<noteq> {} \<or> (path' (E \<inter> (Y-X)\<times>Y) v xs v')"
  using assms(2,3)
  apply (induction xs arbitrary: v)
  using assms(1)
  by auto

lemma subgraph_path': "E' \<subseteq> E \<Longrightarrow> path' E' v vs v' \<Longrightarrow> path' E v vs v'"
  apply (induction vs arbitrary: v) by auto

lemma subgraph_cycle: "E' \<subseteq> E \<Longrightarrow> cycle_node E' v vs \<Longrightarrow> cycle_node E v vs"
  unfolding cycle_node_def
  apply (induction vs arbitrary: v)
  by (auto simp: subgraph_path')

lemma subgraph_cycle_from_node: "E' \<subseteq> E \<Longrightarrow> cycle_from_node E' v vs \<Longrightarrow> cycle_from_node E v vs"
  unfolding cycle_from_node_def
  proof (induction vs arbitrary: v)
    case Nil
    then show ?case by (simp add: cycle_node_def)
  next
    case (Cons a vs)
    then obtain v' where v_v'_sub: "(v,v')\<in>E'\<^sup>*"
      and cycle_v'_sub: "cycle_node E' v' (a # vs)" by fast
    from v_v'_sub Cons.prems(1) have v_v': "(v,v')\<in>E\<^sup>*"
      using rtrancl_mono by auto
    from cycle_v'_sub Cons.prems(1) have cycle_v': "cycle_node E v' (a # vs)"
      by (auto simp: subgraph_cycle)
    with v_v' show ?case by auto
  qed

lemma subgraph_lasso': "E' \<subseteq> E \<Longrightarrow> lasso_from_node' E' v vs \<Longrightarrow> lasso_from_node' E v vs"
  unfolding lasso_from_node'_def
  apply (induction vs arbitrary: v)
  apply blast by (meson subgraph_path')

lemma cycle_from_node_inter_1: "cycle_from_node (E1 \<inter> E2) v vs \<Longrightarrow> cycle_from_node E1 v vs"
  proof -
    assume "cycle_from_node (E1 \<inter> E2) v vs"
    moreover have "(E1 \<inter> E2) \<subseteq> E1" by fast
    ultimately show "cycle_from_node E1 v vs" using subgraph_cycle_from_node by metis
  qed

lemma cycle_from_node_inter_2: "cycle_from_node (E1 \<inter> E2) v vs \<Longrightarrow> cycle_from_node E2 v vs"
  proof -
    assume "cycle_from_node (E1 \<inter> E2) v vs"
    moreover have "(E1 \<inter> E2) \<subseteq> E2" by fast
    ultimately show "cycle_from_node E2 v vs" using subgraph_cycle_from_node by metis
  qed

subsection \<open>Strategies\<close>

locale arena_defs = finite_graph_V +
  fixes V\<^sub>0 :: "'v set"
  fixes prio :: "'v \<Rightarrow> nat"
  assumes V\<^sub>0_in_V: "V\<^sub>0 \<subseteq> V"
begin
  definition V\<^sub>1 where "V\<^sub>1 = V - V\<^sub>0"

  lemma V\<^sub>0_eq_V_min_V\<^sub>1: "V\<^sub>0 = V - V\<^sub>1"
    using V\<^sub>0_in_V
    unfolding V\<^sub>1_def
    by auto

  lemma V\<^sub>1_in_V: "V\<^sub>1 \<subseteq> V"
    using V\<^sub>0_in_V
    unfolding V\<^sub>1_def
    by blast

  lemma V_fst_E: "v \<in> V \<longleftrightarrow> v \<in> fst`E"
    apply rule
    subgoal using succ by force
    subgoal using E_in_V by auto
    done

  lemma players_disjoint: "V\<^sub>0 \<inter> V\<^sub>1 = {}"
    unfolding V\<^sub>1_def by auto

  lemma in_V\<^sub>1_notin_V\<^sub>0: "v\<in>V \<Longrightarrow> v\<notin>V\<^sub>0 \<longleftrightarrow> v\<in>V\<^sub>1"
    unfolding V\<^sub>1_def by blast

  text \<open>A positional strategy for a player i is a function \<sigma>:Vi\<rightarrow>V\<close>
  type_synonym 'a strat = "'a \<Rightarrow> 'a option"

  definition E_of_strat :: "'a strat \<Rightarrow> 'a dgraph" where
    "E_of_strat \<sigma> = {(u,v). \<sigma> u = Some v}"

  lemma E_of_strat_empty[simp]: "E_of_strat Map.empty = {}"
    unfolding E_of_strat_def by fast

  lemma E_of_strat_eq_empty_conv[simp]: "E_of_strat \<sigma> = {} \<longleftrightarrow> \<sigma> = Map.empty"
    unfolding E_of_strat_def by auto

  lemma E_of_strat_dom: "dom \<sigma> = fst`E_of_strat \<sigma>"
    unfolding E_of_strat_def by force

  lemma E_of_strat_dom_node: "v \<in> dom \<sigma> \<longleftrightarrow> v \<in> fst`E_of_strat \<sigma>"
    unfolding E_of_strat_def by force

  lemma E_of_strat_ran: "ran \<sigma> = snd`E_of_strat \<sigma>"
    unfolding E_of_strat_def ran_def by force

  lemma E_of_strat_ran_subset[simp]: "ran \<sigma> \<subseteq> X \<Longrightarrow> E_of_strat \<sigma> `` {x} \<subseteq> X"
    unfolding E_of_strat_def by (auto simp: ranI)

  definition top_priority :: "'v list \<Rightarrow> nat" where
    "top_priority xs \<equiv> MAX v \<in> set xs. prio v"

  abbreviation winning_even :: "'v list \<Rightarrow> bool" where
    "winning_even xs \<equiv> even (top_priority xs)"

  abbreviation winning_odd :: "'v list \<Rightarrow> bool" where
    "winning_odd xs \<equiv> odd (top_priority xs)"

  definition strategy_of :: "'v set \<Rightarrow> 'v strat \<Rightarrow> bool" where
    "strategy_of S \<sigma> \<equiv> dom \<sigma> \<subseteq> S \<and> E_of_strat \<sigma> \<subseteq> E"

  lemma strategy_of_empty[simp]: "strategy_of S Map.empty"
    unfolding strategy_of_def by auto

  lemma strategy_of_map_assign: "\<lbrakk> x\<in>S; (x,y)\<in>E \<rbrakk> \<Longrightarrow> strategy_of S [x\<mapsto>y]"
    unfolding strategy_of_def E_of_strat_def
    by (auto split: if_splits)

  lemma strategy_of_empty_iff_empty_strategy[simp]: "strategy_of {} \<sigma> \<longleftrightarrow> \<sigma> = Map.empty"
    unfolding strategy_of_def by auto

  lemma strategy_of_add_same[simp]: "\<lbrakk> strategy_of S \<sigma>; strategy_of S \<sigma>' \<rbrakk> \<Longrightarrow> strategy_of S (\<sigma> ++ \<sigma>')"
    unfolding strategy_of_def E_of_strat_def by auto

  lemma strategy_of_dom: "\<lbrakk> strategy_of S \<sigma>; v \<in> dom \<sigma> \<rbrakk> \<Longrightarrow> v \<in> S"
    unfolding strategy_of_def by fast

  lemma strategy_of_add_disj: "S \<inter> S' = {} \<Longrightarrow> strategy_of S \<sigma> \<and> strategy_of S' \<sigma>'
    \<Longrightarrow> dom \<sigma> \<inter> dom \<sigma>' = {}"
    unfolding strategy_of_def by blast

  lemma strategies_disjoint: "strategy_of V\<^sub>0 \<sigma> \<and> strategy_of V\<^sub>1 \<sigma>' \<Longrightarrow> dom \<sigma> \<inter> dom \<sigma>' = {}"
    using strategy_of_add_disj players_disjoint by blast

  definition induced_by_strategy :: "'v set \<Rightarrow> 'v strat \<Rightarrow> 'v dgraph" where
    "induced_by_strategy V\<^sub>\<alpha> \<sigma> = E \<inter> ((-V\<^sub>\<alpha>) \<times> UNIV \<union> E_of_strat \<sigma>)"

  lemma induced_by_strategy_empty[simp]: "induced_by_strategy V\<^sub>\<alpha> Map.empty = E \<inter> (-V\<^sub>\<alpha>) \<times> UNIV"
    unfolding induced_by_strategy_def by simp

  lemma ind_subgraph: "induced_by_strategy V\<^sub>\<alpha> \<sigma> \<subseteq> E"
    unfolding induced_by_strategy_def by auto

  lemma ind_subgraph_not_in_dom: "\<lbrakk> (v,w) \<in> E; v \<notin> V\<^sub>\<alpha> \<rbrakk> \<Longrightarrow> (v,w) \<in> induced_by_strategy V\<^sub>\<alpha> \<sigma>"
    unfolding induced_by_strategy_def E_of_strat_def by fast

  lemma ind_subgraph_edge_in_E[simp]: "(v,w) \<in> induced_by_strategy V\<^sub>\<alpha> \<sigma> \<Longrightarrow> (v,w) \<in> E"
    using ind_subgraph by blast

  lemma ind_subgraph_edge_src: "(v,w) \<in> induced_by_strategy V\<^sub>\<alpha> \<sigma> \<Longrightarrow> v \<in> dom \<sigma> \<or> v \<in> (-V\<^sub>\<alpha>)"
    unfolding induced_by_strategy_def E_of_strat_def by auto

  lemma ind_subgraph_edge_dst: "(v,w) \<in> induced_by_strategy V\<^sub>\<alpha> \<sigma> \<Longrightarrow> v \<in> V\<^sub>\<alpha> \<Longrightarrow> w \<in> ran \<sigma>"
    unfolding induced_by_strategy_def E_of_strat_def ran_def by blast

  lemma ind_subgraph_finite[simp]: "finite (induced_by_strategy V\<^sub>\<alpha> \<sigma>)"
    using ind_subgraph fin_E finite_subset by blast

  lemma ind_subgraph_addD: "induced_by_strategy V\<^sub>\<alpha> (\<sigma> ++ \<sigma>') \<subseteq> induced_by_strategy V\<^sub>\<alpha> \<sigma> \<union> E_of_strat \<sigma>'"
    unfolding induced_by_strategy_def E_of_strat_def by auto

  lemma ind_subgraph_add_edge: "(v,w) \<in> induced_by_strategy V\<^sub>\<alpha> (\<sigma> ++ \<sigma>')
    \<Longrightarrow> (v,w) \<in> induced_by_strategy V\<^sub>\<alpha> \<sigma> \<or> (v,w) \<in> induced_by_strategy V\<^sub>\<alpha> \<sigma>'"
    unfolding induced_by_strategy_def E_of_strat_def by fast

  lemma ind_subgraph_add_edge_src: "(v,w) \<in> induced_by_strategy V\<^sub>\<alpha> (\<sigma> ++ \<sigma>')
    \<Longrightarrow> v \<in> dom \<sigma> \<or> v \<in> dom \<sigma>' \<or> v \<in> (-V\<^sub>\<alpha>)"
    unfolding induced_by_strategy_def E_of_strat_def by blast

  lemma ind_subgraph_add_edge_outside_strat: "(v,w) \<in> induced_by_strategy V\<^sub>\<alpha> (\<sigma> ++ \<sigma>') \<Longrightarrow> v \<in> (-V\<^sub>\<alpha>)
    \<Longrightarrow> (v,w) \<in> induced_by_strategy V\<^sub>\<alpha> \<sigma> \<and> (v,w) \<in> induced_by_strategy V\<^sub>\<alpha> \<sigma>'"
    unfolding induced_by_strategy_def E_of_strat_def by fast

  lemma ind_subgraph_add_edge_dom_\<sigma>: "(v,w) \<in> induced_by_strategy V\<^sub>\<alpha> (\<sigma> ++ \<sigma>') \<Longrightarrow> dom \<sigma> \<inter> dom \<sigma>' = {}
       \<Longrightarrow> v \<in> dom \<sigma> \<Longrightarrow> (v,w) \<in> induced_by_strategy V\<^sub>\<alpha> \<sigma>"
      unfolding induced_by_strategy_def E_of_strat_def by auto

  lemma ind_subgraph_add_edge_dom_\<sigma>': "(v,w) \<in> induced_by_strategy V\<^sub>\<alpha> (\<sigma> ++ \<sigma>') \<Longrightarrow> v \<in> dom \<sigma>'
     \<Longrightarrow> (v,w) \<in> induced_by_strategy V\<^sub>\<alpha> \<sigma>'"
    unfolding induced_by_strategy_def E_of_strat_def by blast

  lemma ind_subgraph_to_strategy: "\<lbrakk>(v, w) \<in> induced_by_strategy V\<^sub>\<alpha> \<sigma>; strategy_of V\<^sub>\<alpha> \<sigma>; v \<in> dom \<sigma> \<rbrakk>
    \<Longrightarrow> \<sigma> v = Some w"
    unfolding induced_by_strategy_def strategy_of_def E_of_strat_def by blast

  lemma strategy_to_ind_subgraph: "\<lbrakk>\<sigma> v = Some w; (v,w) \<in> E \<rbrakk> \<Longrightarrow> (v,w) \<in> induced_by_strategy V\<^sub>\<alpha> \<sigma>"
    unfolding induced_by_strategy_def E_of_strat_def by auto

  lemma ind_subgraph_add_disjoint_doms: "\<lbrakk> dom \<sigma> \<inter> dom \<sigma>' = {}; strategy_of V\<^sub>\<alpha> \<sigma> \<rbrakk>
    \<Longrightarrow> induced_by_strategy V\<^sub>\<alpha> \<sigma> \<subseteq> induced_by_strategy V\<^sub>\<alpha> (\<sigma> ++ \<sigma>')"
  proof -
    assume
      doms_disj: "dom \<sigma> \<inter> dom \<sigma>' = {}" and
      strat_of_\<sigma>:  "strategy_of V\<^sub>\<alpha> \<sigma>"

    let ?\<tau> = "\<sigma> ++ \<sigma>'"

    have "\<forall>v w. (v,w) \<in> induced_by_strategy V\<^sub>\<alpha> \<sigma> \<longrightarrow> (v,w) \<in> induced_by_strategy V\<^sub>\<alpha> ?\<tau>"
    proof (intro allI; rule impI)
      fix v w
      assume in_\<sigma>: "(v,w) \<in> induced_by_strategy V\<^sub>\<alpha> \<sigma>"
      hence edge_in_E[simp]: "(v,w) \<in> E" by simp

      from in_\<sigma> consider (own_node) "v \<in> dom \<sigma>" | (opponent_node) "v \<in> -V\<^sub>\<alpha>"
        using ind_subgraph_edge_src by blast
      thus "(v,w) \<in> induced_by_strategy V\<^sub>\<alpha> ?\<tau>" proof cases
        case own_node
        with in_\<sigma> strat_of_\<sigma> have "\<sigma> v = Some w"
          using ind_subgraph_to_strategy by auto
        with doms_disj have "?\<tau> v = Some w"
          using map_add_comm by fastforce
        thus ?thesis
          using strategy_to_ind_subgraph by auto
      next
        case opponent_node thus ?thesis
          unfolding induced_by_strategy_def E_of_strat_def by auto
      qed
    qed

    thus ?thesis by force
  qed

  lemma ind_subgraph_add_disjoint_doms': "\<lbrakk> dom \<sigma> \<inter> dom \<sigma>' = {}; strategy_of V\<^sub>\<alpha> \<sigma>; strategy_of V\<^sub>\<alpha> \<sigma>' \<rbrakk>
    \<Longrightarrow> induced_by_strategy V\<^sub>\<alpha> \<sigma> = induced_by_strategy V\<^sub>\<alpha> (\<sigma> ++ \<sigma>') - dom \<sigma>' \<times> UNIV"
  proof -
    assume
        doms_disj: "dom \<sigma> \<inter> dom \<sigma>' = {}" and
        strat_of_\<sigma>: "strategy_of V\<^sub>\<alpha> \<sigma>" and
        strat_of_\<sigma>': "strategy_of V\<^sub>\<alpha> \<sigma>'"

    let ?\<tau> = "\<sigma> ++ \<sigma>'"
    from strat_of_\<sigma> strat_of_\<sigma>' have strat_of_\<tau>: "strategy_of V\<^sub>\<alpha> ?\<tau>" by simp

    have "\<forall>v w. (v,w) \<in> induced_by_strategy V\<^sub>\<alpha> \<sigma> \<longrightarrow> (v,w) \<in> induced_by_strategy V\<^sub>\<alpha> ?\<tau> - dom \<sigma>' \<times> UNIV"
    proof (intro allI; rule impI)
      fix v w
      assume in_\<sigma>: "(v,w) \<in> induced_by_strategy V\<^sub>\<alpha> \<sigma>"
      hence edge_in_E[simp]: "(v,w) \<in> E" by simp

      from in_\<sigma> consider (own_node) "v \<in> dom \<sigma>" | (opponent_node) "v \<in> -V\<^sub>\<alpha>"
        using ind_subgraph_edge_src by blast
      thus "(v,w) \<in> induced_by_strategy V\<^sub>\<alpha> ?\<tau> - dom \<sigma>' \<times> UNIV" proof cases
        case own_node
        with in_\<sigma> strat_of_\<sigma> have "\<sigma> v = Some w"
          using ind_subgraph_to_strategy by auto
        with doms_disj have edge_in_\<sigma>: "?\<tau> v = Some w"
          using map_add_comm by fastforce
        from own_node strat_of_\<sigma>' doms_disj have v_notin_dom_\<sigma>': "v \<notin> dom \<sigma>'"
          using ind_subgraph_edge_src[OF in_\<sigma>] by auto
        from edge_in_\<sigma> v_notin_dom_\<sigma>' show ?thesis
          using strategy_to_ind_subgraph by auto
      next
        case opponent_node
        with strat_of_\<sigma>' have "v \<notin> dom \<sigma>'"
          unfolding strategy_of_def
          using ind_subgraph_edge_src[OF in_\<sigma>]
          by auto
        with opponent_node show ?thesis
          unfolding induced_by_strategy_def E_of_strat_def by auto
      qed
    qed

    moreover have "\<forall>v w. (v,w) \<in> induced_by_strategy V\<^sub>\<alpha> ?\<tau> - dom \<sigma>' \<times> UNIV \<longrightarrow> (v,w) \<in> induced_by_strategy V\<^sub>\<alpha> \<sigma>"
    proof (intro allI; rule impI)
      fix v w
      assume in_\<sigma>': "(v,w) \<in> induced_by_strategy V\<^sub>\<alpha> ?\<tau> - dom \<sigma>' \<times> UNIV"
      hence edge_in_E[simp]: "(v,w) \<in> E" by force

      from in_\<sigma>' consider (own_node) "v \<in> dom ?\<tau> - dom \<sigma>'" | (opponent_node) "v \<in> -V\<^sub>\<alpha>"
        using ind_subgraph_edge_src by fastforce
      thus "(v,w) \<in> induced_by_strategy V\<^sub>\<alpha> \<sigma>" proof cases
        case own_node
        with in_\<sigma>' strat_of_\<tau> have "?\<tau> v = Some w"
          using ind_subgraph_to_strategy by fastforce
        with own_node doms_disj have "\<sigma> v = Some w"
          using map_add_comm by blast
        thus ?thesis using strategy_to_ind_subgraph by force
      next
        case opponent_node thus ?thesis
          unfolding induced_by_strategy_def E_of_strat_def by auto
      qed
    qed

    ultimately show ?thesis by fast
  qed

  lemma ind_subgraph_cycle: "cycle_node (induced_by_strategy V\<^sub>\<alpha> \<sigma>) v xs \<Longrightarrow> cycle_node E v xs"
    using subgraph_cycle by (metis ind_subgraph)

  lemma ind_subgraph_cycle_from_node: "cycle_from_node (induced_by_strategy V\<^sub>\<alpha> \<sigma>) v xs
     \<Longrightarrow> cycle_from_node E v xs"
    using subgraph_cycle_from_node by (metis ind_subgraph)

  lemma ind_subgraph_lasso': "lasso_from_node' (induced_by_strategy V\<^sub>\<alpha> \<sigma>) v xs
    \<Longrightarrow> lasso_from_node' E v xs"
    using subgraph_lasso' by (metis ind_subgraph)

end

locale player_arena = arena_defs E V V\<^sub>0 prio
  for E V and V\<^sub>0 :: "'v set" and prio
 +
  fixes V\<^sub>\<alpha> :: "'v set"
  fixes winningP :: "nat \<Rightarrow> bool"
  assumes V\<^sub>\<alpha>_subset: "V\<^sub>\<alpha> \<subseteq> V"

  (* assumes "V\<^sub>\<alpha> = V\<^sub>0 \<or> V\<^sub>\<alpha> = V-V\<^sub>0" *)
begin
  abbreviation (input) owned_target :: "'v set \<Rightarrow> 'v set" where
    "owned_target Y \<equiv> {v|v. v\<in>V\<^sub>\<alpha> \<and> E``{v} \<inter> Y \<noteq> {}}"

  abbreviation (input) opponent_target :: "'v set \<Rightarrow> 'v set" where
    "opponent_target Y \<equiv> {v|v. v\<in>-V\<^sub>\<alpha> \<and> E``{v} \<subseteq> Y}"

  inductive is_attractor :: "'v set \<Rightarrow> 'v set \<Rightarrow> bool" for X where
    base: "is_attractor X X" |
    step: "is_attractor X Y \<Longrightarrow> Y' = Y \<union> owned_target Y \<union> opponent_target Y \<Longrightarrow>  is_attractor X Y'"

  inductive_set attractor :: "'v set \<Rightarrow> 'v set" for X where
    base: "x \<in> X \<Longrightarrow> x \<in> attractor X"
  | own: "\<lbrakk> x \<in> V\<^sub>\<alpha>-X; (x,y)\<in>E; y\<in>attractor X \<rbrakk> \<Longrightarrow> x \<in> attractor X"
  | opponent: "\<lbrakk> x\<in>V-V\<^sub>\<alpha>-X; \<forall>y. (x,y)\<in>E \<longrightarrow> y\<in>attractor X \<rbrakk> \<Longrightarrow> x \<in> attractor X"

  lemma attractor_subset: "X \<subseteq> attractor X"
    by (auto intro: base)

  inductive_set attractor_edges :: "'v set \<Rightarrow> ('v \<times> 'v) set" for X where
    ae_base: "x \<in> X \<Longrightarrow> (x,x) \<in> attractor_edges X"
  | ae_own: "\<lbrakk> x \<in> V\<^sub>\<alpha>; (x,y)\<in>E; (y,y_tgt)\<in>attractor_edges X \<rbrakk> \<Longrightarrow> (x,y) \<in> attractor_edges X"
  | ae_opponent: "\<lbrakk> x\<in>V-V\<^sub>\<alpha>; \<forall>y. (x,y)\<in>E \<longrightarrow> (\<exists>y_tgt. (y,y_tgt)\<in>attractor_edges X) \<rbrakk> \<Longrightarrow> (x,x) \<in> attractor_edges X"

  lemma attractor_edges_sound: "(x,y)\<in>attractor_edges X \<Longrightarrow> x\<in>attractor X"
    apply (induction rule: attractor_edges.induct)
    by (auto intro: base own opponent)

  lemma attractor_edges_complete: "x\<in>attractor X \<Longrightarrow> (\<exists>y. (x,y)\<in>attractor_edges X)"
    apply (induction rule: attractor.induct)
    by (auto 0 3 intro: ae_base ae_own ae_opponent)

  lemma attractor_edges_edges: "(x,y)\<in>attractor_edges X \<Longrightarrow> x\<in>V\<^sub>\<alpha>-X \<Longrightarrow>(x,y)\<in>E"
    apply (induction rule: attractor_edges.induct)
    by (auto intro: base own opponent)

  definition "attractor_strategy X v \<equiv>
    if v\<notin>X \<and> v\<in>V\<^sub>\<alpha> \<and> (\<exists>v'. (v,v')\<in>attractor_edges X) then
      Some (SOME v'. (v,v')\<in>attractor_edges X)
    else
      None
      "

  lemma attractor_strategy_edges: "attractor_strategy X v = Some v' \<Longrightarrow> (v,v') \<in> attractor_edges X"
    unfolding attractor_strategy_def
    by (auto split: if_splits dest!: sym[of _ v'] intro: someI)

  lemma attractor_strategy_edges_E: "attractor_strategy X v = Some v' \<Longrightarrow> (v,v') \<in> E"
  proof -
    assume assm: "attractor_strategy X v = Some v'"
    from assm have A: "(v,v') \<in> attractor_edges X" using attractor_strategy_edges by auto
    from assm have B: "v\<in>V\<^sub>\<alpha>-X" by (auto simp: attractor_strategy_def split: if_splits)
    from attractor_edges_edges[OF A B] show "(v,v') \<in> E" .
  qed

  lemma attractor_strategy_sound: "attractor_strategy X v = Some v' \<Longrightarrow> v \<in> attractor X"
  proof -
    assume assm: "attractor_strategy X v = Some v'"
    hence "(v,v') \<in> attractor_edges X" using attractor_strategy_edges by auto
    from attractor_edges_sound[OF this] show ?thesis .
  qed

  lemma "attractor_strategy X v = Some v' \<Longrightarrow> v' \<in> attractor X"
    apply (auto simp: attractor_strategy_def split: if_splits)
    by (metis attractor_edges.simps attractor_edges_sound someI)

  lemma dom_attractor_strategy: "dom (attractor_strategy X) = V\<^sub>\<alpha> \<inter> (attractor X - X)"
    by (auto simp: attractor_strategy_def split: if_splits intro: attractor_edges_sound attractor_edges_complete)

  lemma attractor_strategy_of_V\<^sub>\<alpha>: "strategy_of V\<^sub>\<alpha> (attractor_strategy X)"
    unfolding attractor_strategy_def strategy_of_def E_of_strat_def
    apply (auto split: if_splits)
    using attractor_edges_edges tfl_some by auto

  lemma attractor_strategy_closed_edge: "(x,y) \<in> induced_by_strategy V\<^sub>\<alpha> (attractor_strategy X) \<Longrightarrow> x \<in> attractor X - X
    \<Longrightarrow> y \<in> attractor X"
    unfolding induced_by_strategy_def E_of_strat_def attractor_strategy_def
    using attractor.cases apply (auto split: if_splits)
    by (metis attractor_edges.simps attractor_edges_sound someI)

  lemma attractor_strategy_closed: "induced_by_strategy V\<^sub>\<alpha> (attractor_strategy X) `` (attractor X - X) \<subseteq> attractor X"
    using attractor_strategy_closed_edge by blast

  lemma attractor_strategy_escape_via_X: "(x,y) \<in> induced_by_strategy V\<^sub>\<alpha> (attractor_strategy X)
     \<Longrightarrow> x \<in> attractor X \<Longrightarrow> y \<notin> attractor X \<Longrightarrow> x \<in> X"
  proof (rule ccontr)
    assume assms: "(x,y) \<in> induced_by_strategy V\<^sub>\<alpha> (attractor_strategy X)"
                  "x \<in> attractor X"
                  "y \<notin> attractor X"
                  "x\<notin>X"
    then show False proof (cases "x\<in>X")
      case True with assms(4) show ?thesis ..
    next
      case False
      with assms(2) have "x\<in>attractor X - X" by blast
      from attractor_strategy_closed_edge[OF assms(1) this] have "y \<in> attractor X" .
      with assms(3) show ?thesis ..
    qed
  qed

  inductive attractor'p :: "'v set \<Rightarrow> nat \<Rightarrow> 'v \<Rightarrow> bool" for X where
    base: "\<lbrakk> x \<in> X \<rbrakk> \<Longrightarrow> attractor'p X 0 x"
  | own: "\<lbrakk> x \<in> V\<^sub>\<alpha>-X; (x,y)\<in>E; attractor'p X i y \<rbrakk> \<Longrightarrow> attractor'p X (Suc i) x"
  | opponent: "\<lbrakk> x\<in>V-V\<^sub>\<alpha>-X; \<forall>y. (x,y)\<in>E \<longrightarrow> attractor'p X i y \<rbrakk> \<Longrightarrow> attractor'p X (Suc i) x"

  definition "attractor' X i \<equiv> Collect (attractor'p X i)"

  lemma attractor'_induct[consumes 1, case_names base own opponent]:
    assumes "x\<in>attractor' X i"
      and "\<And>x. x \<in> X \<Longrightarrow> P 0 x"
      and "\<And>x y i. \<lbrakk>x \<in> V\<^sub>\<alpha> - X; (x, y) \<in> E; y\<in>attractor' X i; P i y\<rbrakk> \<Longrightarrow> P (Suc i) x"
      and "\<And>x i. \<lbrakk>x \<in> V - V\<^sub>\<alpha> - X; \<forall>y. (x, y) \<in> E \<longrightarrow> y\<in>attractor' X i \<and> P i y\<rbrakk> \<Longrightarrow> P (Suc i) x"
    shows "P i x"
    using attractor'p.induct[of _ i x P] assms
    unfolding attractor'_def
    by auto

  context
    fixes X :: "'v set"
  begin
    fun nodes_in_rank :: "nat \<Rightarrow> 'v set" where
      "nodes_in_rank 0 = X"
    | "nodes_in_rank (Suc n) =
        nodes_in_rank n
      \<union> { x | x y :: 'v. x\<in>V\<^sub>\<alpha> \<and> (x,y)\<in>E \<and> y\<in>nodes_in_rank n }
      \<union> { x. x\<in>V-V\<^sub>\<alpha> \<and> (\<forall>y. (x,y)\<in>E \<longrightarrow> y\<in>nodes_in_rank n)  }
        "

    lemma nodes_in_rank_mono: "n\<le>m \<Longrightarrow> nodes_in_rank n \<subseteq> nodes_in_rank m"
      apply (induction m)
      by (auto simp: le_Suc_eq)

    lemma nodes_in_rank_increasing: "nodes_in_rank (n-Suc 0) \<subseteq> nodes_in_rank n"
      apply (cases n)
      by auto

    lemma nodes_in_rank_ss_attractor: "x\<in>nodes_in_rank n \<Longrightarrow> x\<in>attractor X"
      apply (induction n arbitrary: x)
      by (auto intro: attractor.intros)

    lemma attractor_ss_nodes_in_rank: "x\<in>attractor X \<Longrightarrow> (\<exists>n. x\<in>nodes_in_rank n)"
    proof (induction rule: attractor.induct)
      case (base x)
      then show ?case by (auto intro: exI[where x=0])
    next
      case (own x y)
      then show ?case
        apply clarsimp
        subgoal for n by (auto intro!: exI[where x="Suc n"])
        done
    next
      case (opponent x)
      define n_of_y where "n_of_y \<equiv> \<lambda>y. SOME n. y \<in> nodes_in_rank n"
      define n_max where "n_max \<equiv> MAX y\<in>E``{x}. n_of_y y"

      have "n_of_y ` E `` {x} \<noteq> {}" using opponent.hyps succ by auto
      have FIN: "finite (n_of_y ` E `` {x})" by auto

      have n_of_y: "(x,y)\<in>E \<Longrightarrow> y\<in>nodes_in_rank (n_of_y y)" for y
        unfolding n_of_y_def
        using opponent.IH
        by (auto intro: someI)

      have "(x,y)\<in>E \<Longrightarrow> (\<exists>i\<le>n_max. y\<in>nodes_in_rank i)" for y
        using Max_ge[OF FIN] n_of_y unfolding n_max_def
        by blast
      hence "(x,y)\<in>E \<Longrightarrow> y\<in>nodes_in_rank n_max" for y
        using nodes_in_rank_mono by auto
      then show ?case
        apply (rule_tac exI[where x="Suc n_max"])
        using opponent.hyps
        by simp
    qed

    lemma attractor_eq_nodes_in_rank: "attractor X = \<Union>(nodes_in_rank`UNIV)"
      using attractor_ss_nodes_in_rank nodes_in_rank_ss_attractor by auto

    lemma nodes_in_rank_edges_same: "\<lbrakk>x' \<in> nodes_in_rank n'; x' \<notin> X; (x', y') \<in> E; x' \<notin> V\<^sub>\<alpha>\<rbrakk> \<Longrightarrow> y' \<in> nodes_in_rank n'"
      apply (induction n') by auto

    lemma nodes_in_rank_edges_lower: "\<lbrakk>x \<in> nodes_in_rank (Suc n); x \<notin> X; (x,y) \<in> E; x \<notin> V\<^sub>\<alpha>\<rbrakk> \<Longrightarrow> y \<in> nodes_in_rank n"
      apply (induction n arbitrary: x) by auto

    lemma nodes_in_rank_forces_X: "\<exists>\<sigma>.
      strategy_of V\<^sub>\<alpha> \<sigma> \<and> dom \<sigma> \<subseteq> nodes_in_rank n - X
      \<and> (\<forall>n'. \<forall>x' \<in> nodes_in_rank n' - X. (\<forall>y' \<in> (induced_by_strategy V\<^sub>\<alpha> \<sigma>) `` {x'}. y' \<in> nodes_in_rank (n')))
      \<and> (\<forall>x\<in>nodes_in_rank n. \<forall>xs z. path' (induced_by_strategy V\<^sub>\<alpha> \<sigma>) x xs z \<and> n<length xs \<longrightarrow> set xs \<inter> X \<noteq> {})"
    proof (induction n)
      case 0
      then show ?case
        apply (rule_tac exI[where x=Map.empty])
        apply (intro conjI; simp)
        subgoal using nodes_in_rank_edges_same by blast
        subgoal using origin_in_path' by fastforce
        done

    next
      case (Suc n)
      from Suc.IH obtain \<sigma> where
        strat_\<sigma>: "strategy_of V\<^sub>\<alpha> \<sigma>" and
        dom_\<sigma>: "dom \<sigma> \<subseteq> nodes_in_rank n - X" and
        closed_\<sigma>: "(\<forall>n'. \<forall>x' \<in> nodes_in_rank n' - X. (\<forall>y' \<in> (induced_by_strategy V\<^sub>\<alpha> \<sigma>) `` {x'}. y' \<in> nodes_in_rank (n')))" and
        forces_\<sigma>: "\<And>x xs z. \<lbrakk>x\<in>nodes_in_rank n; path' (induced_by_strategy V\<^sub>\<alpha> \<sigma>) x xs z; n < length xs\<rbrakk> \<Longrightarrow> set xs \<inter> X \<noteq> {}"
        by blast

      define new_player_nodes where "new_player_nodes = (nodes_in_rank (Suc n) - nodes_in_rank n) \<inter> V\<^sub>\<alpha>"
      define target where "target = (\<lambda>x. SOME x'. x'\<in>nodes_in_rank n \<and> (x,x')\<in>E)"

      {
        fix x
        assume "x\<in>new_player_nodes"
        then have "target x\<in>nodes_in_rank n" "(x,target x)\<in>E"
          unfolding new_player_nodes_def target_def
          apply (simp_all)
          by (metis (no_types, lifting) someI)+
      } note target=this

      have target_eq: "x\<in>new_player_nodes \<longleftrightarrow> (x\<in>nodes_in_rank (Suc n) \<and> x\<in>V\<^sub>\<alpha> \<and> x\<notin>nodes_in_rank n \<and> target x\<in>nodes_in_rank n\<and> (x,target x)\<in>E)" for x
        unfolding new_player_nodes_def target_def
        apply (simp_all)
        apply auto []
        by (metis (no_types, lifting) someI)+

      define \<sigma>' where "\<sigma>' = (\<lambda>x. if x \<in> new_player_nodes then Some (target x) else \<sigma> x)"

      show ?case
      proof (intro exI[where x=\<sigma>'] conjI allI ballI impI; (elim conjE)?)
        show "strategy_of V\<^sub>\<alpha> \<sigma>'"
          using strat_\<sigma>
          unfolding \<sigma>'_def strategy_of_def E_of_strat_def
          apply (safe; simp split: if_splits)
          using target_eq by blast+

        show "dom \<sigma>' \<subseteq> nodes_in_rank (Suc n) - X"
          unfolding \<sigma>'_def
          using dom_\<sigma>
          apply (safe; simp split: if_splits)
          using target_eq nodes_in_rank_mono nodes_in_rank.simps by blast+

        {
          fix n' x' y'
          assume "x' \<in> nodes_in_rank n' - X" "y' \<in> induced_by_strategy V\<^sub>\<alpha> \<sigma>' `` {x'}"
          then show "y' \<in> nodes_in_rank n'"
            using closed_\<sigma> nodes_in_rank_mono
            unfolding \<sigma>'_def induced_by_strategy_def E_of_strat_def
            apply (simp split: if_splits)
            apply (simp add: target_eq)
            by (meson in_mono nle_le)
        } note closed_\<sigma>'=this

        {
          fix x xs z
          assume "x\<in>nodes_in_rank n"
            and "path' (induced_by_strategy V\<^sub>\<alpha> \<sigma>') x xs z"
            and "X \<inter> set xs = {}"
          then have "path' (induced_by_strategy V\<^sub>\<alpha> \<sigma>) x xs z"
          proof (induction xs arbitrary: x)
            case Nil thus ?case by fastforce
          next
            case (Cons a xs')

            from Cons(3) have a_is_x[simp]: "a=x" by simp
            with Cons obtain x' where x'_edge: "(x,x') \<in> induced_by_strategy V\<^sub>\<alpha> \<sigma>'"
              and x'_path_\<sigma>': "path' (induced_by_strategy V\<^sub>\<alpha> \<sigma>')  x' xs' z" by auto

            from x'_edge closed_\<sigma>' have "x' \<in> nodes_in_rank n"
              using Cons.prems(1) Cons.prems(3) by auto
            from Cons.IH[OF this x'_path_\<sigma>'] Cons.prems have x'_path_\<sigma>:
              "path' (induced_by_strategy V\<^sub>\<alpha> \<sigma>) x' xs' z" by simp

            have "(x,x') \<in> induced_by_strategy V\<^sub>\<alpha> \<sigma>"
              using Cons.prems(1) x'_edge
              unfolding \<sigma>'_def new_player_nodes_def induced_by_strategy_def E_of_strat_def
              by simp

            then show ?case using x'_path_\<sigma> by auto
          qed
        } note xfer_lower_rank_path = this

        {
          fix x xs z
          assume
            X_IN_SUCN: "x \<in> nodes_in_rank (Suc n)"
            and PATH': "path' (induced_by_strategy V\<^sub>\<alpha> \<sigma>') x xs z"
            and LEN: "Suc n < length xs"

          from X_IN_SUCN consider
            (already_in) "x\<in>nodes_in_rank n"
            | (our_node) "x\<notin>nodes_in_rank n" "x\<in>V\<^sub>\<alpha>" "(x,target x)\<in>E" "target x\<in>nodes_in_rank n"
            | (opponent_node) "x\<notin>nodes_in_rank n" "x\<in>V-V\<^sub>\<alpha>" "\<forall>y\<in>E``{x}. y\<in>nodes_in_rank n"
            apply simp
            using IntI X_IN_SUCN new_player_nodes_def target_eq by blast

          then show "set xs \<inter> X \<noteq> {}"
          proof cases
            case already_in thus ?thesis
              using Suc_lessD PATH' LEN forces_\<sigma> xfer_lower_rank_path by fast

          next
            case our_node
            then have "(x,x')\<in>induced_by_strategy V\<^sub>\<alpha> \<sigma>' \<Longrightarrow> x'=target x" for x'
              unfolding induced_by_strategy_def E_of_strat_def \<sigma>'_def
              using X_IN_SUCN
              by (auto split: if_splits simp: target_eq)
            then obtain xs' where xs': "xs=x#xs'" "path' (induced_by_strategy V\<^sub>\<alpha> \<sigma>') (target x) xs' z"
              using LEN PATH'
              by (cases xs) auto

            show "set xs \<inter> X \<noteq> {}"
            proof
              assume XS_dj_X: "set xs \<inter> X = {}"
              from xfer_lower_rank_path[OF _ xs'(2)] XS_dj_X xs'(1) \<open>target x \<in> nodes_in_rank n\<close>
              have "path' (induced_by_strategy V\<^sub>\<alpha> \<sigma>) (target x) xs' z" by auto
              from forces_\<sigma>[OF _ this] LEN \<open>target x \<in> nodes_in_rank n\<close> xs'(1) XS_dj_X show False by auto
            qed
          next
            case opponent_node

            then obtain xs' y where xs': "xs=x#xs'" "path' (induced_by_strategy V\<^sub>\<alpha> \<sigma>') y xs' z" "y\<in>nodes_in_rank n"
              using LEN PATH'
              by (cases xs) auto

            show "set xs \<inter> X \<noteq> {}"
            proof
              assume XS_dj_X: "set xs \<inter> X = {}"

              from xfer_lower_rank_path[OF _ xs'(2)] XS_dj_X xs'(1,3)
              have "path' (induced_by_strategy V\<^sub>\<alpha> \<sigma>) y xs' z" by auto

              from forces_\<sigma>[OF _ this] LEN \<open>y \<in> nodes_in_rank n\<close> xs'(1) XS_dj_X show False by auto
            qed
          qed
        }
      qed
    qed (** proof nodes_in_rank_forces_X *)
  end (** context fixed X *)

  lemma nodes_in_rank_ss: "nodes_in_rank X n \<subseteq> X \<union> V"
    apply (induction n)
    using V\<^sub>\<alpha>_subset
    by auto

  lemma nodes_in_rank_finite[simp, intro!]: "finite X \<Longrightarrow> finite (nodes_in_rank X n)"
    by (metis fin_V finite_Un finite_subset nodes_in_rank_ss)

  lemma nodes_in_rank_finite': "finite (nodes_in_rank X n - X)"
    by (meson Diff_subset_conv fin_V finite_subset nodes_in_rank_ss)

  lemma attractor_ss: "attractor X \<subseteq> X \<union> V"
  proof
    fix x
    assume "x\<in>attractor X"
    then show "x\<in>X\<union>V"
      apply (induction rule: attractor.induct)
      using V\<^sub>\<alpha>_subset
      by auto
  qed

  lemma finite_union_nat_range_bound:
    fixes f :: "nat \<Rightarrow> 'a set"
    assumes FIN: "finite (\<Union>(range f))"
    assumes MONO: "\<And>n n'. n\<le>n' \<Longrightarrow> f n \<subseteq> f n'"
    shows "\<exists>n. \<Union>(range f) = f n"
  proof -
    obtain n where "\<Union>(range f) = \<Union>{f i | i . i\<le>n}"
    proof -
      from finite_subset_image[OF finite_UnionD[OF FIN] order_refl]
      obtain C where 1: "finite C" "range f = f`C" by auto
      then obtain n where "C \<subseteq> {0..n}"
        by (meson atLeastAtMost_iff finite_nat_set_iff_bounded_le subset_eq zero_le)
      with 1 have "range f = f`{0..n}" by auto
      thus thesis by (force intro!: that[of n])
    qed
    also have "\<dots> = f n"
      using MONO
      by auto
    finally show ?thesis ..
  qed

  lemma finite_attractor: "finite (attractor X - X)"
    by (meson Diff_subset_conv attractor_ss fin_V rev_finite_subset)

  lemma attractor_max_rank_eq: "\<exists>n. attractor X = nodes_in_rank X n"
  proof -
    have 1: "\<Union>(range (nodes_in_rank X)) - X = \<Union>(range (\<lambda>x. nodes_in_rank X x - X))" by auto

    have "\<exists>n. attractor X - X = nodes_in_rank X n - X"
      using finite_attractor
      unfolding attractor_eq_nodes_in_rank
      apply (subst 1)
      apply (rule finite_union_nat_range_bound)
      apply simp
      by (simp add: Diff_mono nodes_in_rank_mono)

    thus ?thesis
      by (metis Diff_partition attractor_subset bot_nat_0.extremum nodes_in_rank.simps(1) nodes_in_rank_mono)
  qed

  lemma attractor_attracts: "\<exists>\<sigma>.
    strategy_of V\<^sub>\<alpha> \<sigma> \<and> (\<forall>v\<in>attractor X. \<forall>xs. lasso_from_node' (induced_by_strategy V\<^sub>\<alpha> \<sigma>) v xs \<longrightarrow> set xs \<inter> X \<noteq> {})"
  proof -
    obtain n where attr_x_rank_n: "attractor X = nodes_in_rank X n"
      using attractor_max_rank_eq by blast

    from nodes_in_rank_forces_X[of X n] obtain \<sigma> where
      strat_\<sigma>: "strategy_of V\<^sub>\<alpha> \<sigma>" and
      dom_\<sigma>: "dom \<sigma> \<subseteq> nodes_in_rank X n - X" and
      closed_\<sigma>: "(\<forall>n'. \<forall>x'\<in>nodes_in_rank X n' - X. \<forall>y'\<in>induced_by_strategy V\<^sub>\<alpha> \<sigma> `` {x'}. y' \<in> nodes_in_rank X n')" and
      forces_\<sigma>: "(\<forall>x\<in>nodes_in_rank X n. \<forall>xs z. path' (induced_by_strategy V\<^sub>\<alpha> \<sigma>) x xs z \<and> n < length xs \<longrightarrow> set xs \<inter> X \<noteq> {})"
      by blast

    show ?thesis
    proof (rule exI[where x=\<sigma>]; intro conjI ballI impI allI)
      show "strategy_of V\<^sub>\<alpha> \<sigma>" by fact

      fix v xs
      assume v_in_attr: "v \<in> attractor X"
         and lasso_v_xs: "lasso_from_node' (induced_by_strategy V\<^sub>\<alpha> \<sigma>) v xs"

      from v_in_attr attr_x_rank_n have v_in_rank_n: "v \<in> nodes_in_rank X n" by simp

      from lasso'_extend_any_length[of "(induced_by_strategy V\<^sub>\<alpha> \<sigma>)" v xs n, OF lasso_v_xs]
      obtain xs' where
        len_xs': "n < length xs'" and
        set_xs'_eq: "set xs = set xs'" and
        lasso_xs': "lasso_from_node' (induced_by_strategy V\<^sub>\<alpha> \<sigma>) v xs'"
        by blast

      from lasso'_impl_path[of "(induced_by_strategy V\<^sub>\<alpha> \<sigma>)" v xs', OF lasso_xs']
      obtain v' where "path' (induced_by_strategy V\<^sub>\<alpha> \<sigma>) v xs' v'" ..

      hence "set xs' \<inter> X \<noteq> {}" using forces_\<sigma> v_in_rank_n len_xs' by blast
      with set_xs'_eq show "set xs \<inter> X \<noteq> {}" by simp
    qed
  qed
end (** locale player_arena *)

context player_arena begin

  abbreviation "winning_player xs \<equiv> winningP (top_priority xs)"
  abbreviation "winning_opponent xs \<equiv> \<not>winningP (top_priority xs)"

  definition won_by_player :: "'v \<Rightarrow> bool" where
    "won_by_player v \<equiv> v\<in>V \<and> (\<exists>\<sigma>. strategy_of V\<^sub>\<alpha> \<sigma> \<and>
    (\<forall>xs. cycle_from_node (induced_by_strategy (dom \<sigma>) \<sigma>) v xs \<longrightarrow> winning_player xs))"

  lemma "won_by_player v \<Longrightarrow> (\<exists>\<sigma>. strategy_of V\<^sub>\<alpha> \<sigma> \<and>
    (\<forall>xs. cycle_from_node (induced_by_strategy (dom \<sigma>) \<sigma>) v xs \<longrightarrow> \<not>winning_opponent xs))"
    unfolding won_by_player_def by auto

  definition won_by_opponent :: "'v \<Rightarrow> bool" where
    "won_by_opponent v \<equiv> v\<in>V \<and> (\<exists>\<sigma>. strategy_of (V-V\<^sub>\<alpha>) \<sigma> \<and>
    (\<forall>xs. cycle_from_node (induced_by_strategy (dom \<sigma>) \<sigma>) v xs \<longrightarrow> winning_opponent xs))"

  lemma "won_by_opponent v \<Longrightarrow> (\<exists>\<sigma>. strategy_of (V-V\<^sub>\<alpha>) \<sigma> \<and>
    (\<forall>xs. cycle_from_node (induced_by_strategy (dom \<sigma>) \<sigma>) v xs \<longrightarrow> \<not>winning_player xs))"
    unfolding won_by_opponent_def by auto

  lemma V\<^sub>\<alpha>_induced_succs_1: "v\<in>V\<^sub>\<alpha> \<Longrightarrow> strategy_of (V-V\<^sub>\<alpha>) \<sigma>' \<Longrightarrow> induced_by_strategy (dom \<sigma>') \<sigma>' `` {v} = E `` {v}"
    unfolding induced_by_strategy_def E_of_strat_def strategy_of_def V\<^sub>1_def by auto

  lemma V\<^sub>\<alpha>_induced_succs_2: "v\<in>V\<^sub>\<alpha> \<Longrightarrow> strategy_of V\<^sub>\<alpha> \<sigma> \<Longrightarrow> induced_by_strategy (dom \<sigma>) \<sigma> `` {v} \<noteq> {}"
    unfolding induced_by_strategy_def E_of_strat_def strategy_of_def
    using succ[of v] V\<^sub>\<alpha>_subset
    apply (cases "v\<in>dom \<sigma>")
    subgoal by auto
    subgoal by blast
    done

  lemma V_opp_induced_succs_1: "v\<in>-V\<^sub>\<alpha> \<Longrightarrow> strategy_of V\<^sub>\<alpha> \<sigma>' \<Longrightarrow> induced_by_strategy (dom \<sigma>') \<sigma>' `` {v} = E `` {v}"
    unfolding induced_by_strategy_def E_of_strat_def strategy_of_def V\<^sub>1_def by auto

  lemma V_opp_induced_succs_2: "v\<in>V-V\<^sub>\<alpha> \<Longrightarrow> strategy_of (V-V\<^sub>\<alpha>) \<sigma> \<Longrightarrow> induced_by_strategy (dom \<sigma>) \<sigma> `` {v} \<noteq> {}"
    unfolding induced_by_strategy_def E_of_strat_def strategy_of_def V\<^sub>1_def
    using succ[of v] apply (cases "v\<in>dom \<sigma>") by auto

  lemma w1: "won_by_player v \<Longrightarrow> \<not>won_by_opponent v"
    unfolding won_by_player_def won_by_opponent_def
  proof clarsimp
    fix \<sigma> \<sigma>'
    define G\<sigma> where "G\<sigma> = induced_by_strategy (dom \<sigma>) \<sigma>"
    define G\<sigma>' where "G\<sigma>' = induced_by_strategy (dom \<sigma>') \<sigma>'"
    assume \<sigma>_player: "strategy_of V\<^sub>\<alpha> \<sigma>"
      and \<sigma>_win: "\<forall>xs. cycle_from_node G\<sigma> v xs \<longrightarrow> winningP (top_priority xs)"
      and \<sigma>'_opp: "strategy_of (V-V\<^sub>\<alpha>) \<sigma>'"
      and "v\<in>V"
    interpret Ginter: arena_defs "G\<sigma> \<inter> G\<sigma>'" V V\<^sub>0 prio
      apply unfold_locales
      subgoal unfolding G\<sigma>_def using ind_subgraph E_in_V by blast
      subgoal by simp
      subgoal proof cases
        fix v
        assume v_in_V\<^sub>\<alpha>: "v\<in>V\<^sub>\<alpha>"
        with \<sigma>'_opp have "G\<sigma>' `` {v} = E `` {v}"
          unfolding G\<sigma>'_def by (simp add: V\<^sub>\<alpha>_induced_succs_1)
        moreover from v_in_V\<^sub>\<alpha> \<sigma>_player have "G\<sigma> `` {v} \<noteq> {}"
          unfolding G\<sigma>_def by (simp add: V\<^sub>\<alpha>_induced_succs_2)
        moreover note succ[of v]
        moreover have "G\<sigma> \<subseteq> E" using ind_subgraph E_in_V by (simp add: G\<sigma>_def)
        ultimately show "(G\<sigma> \<inter> G\<sigma>') `` {v} \<noteq> {}" by fast
      next
        fix v
        assume "v\<in>V" "v\<notin>V\<^sub>\<alpha>"
        hence v_in_Vopp: "v\<in>V-V\<^sub>\<alpha>" by auto
        with \<sigma>_player have "G\<sigma> `` {v} = E `` {v}"
          unfolding G\<sigma>_def by (simp add: V_opp_induced_succs_1)
        moreover from v_in_Vopp \<sigma>'_opp have "G\<sigma>' `` {v} \<noteq> {}"
          unfolding G\<sigma>'_def by (simp add: V_opp_induced_succs_2)
        moreover note succ[of v]
        moreover have "G\<sigma>' \<subseteq> E" using ind_subgraph E_in_V by (simp add: G\<sigma>'_def)
        ultimately show "(G\<sigma> \<inter> G\<sigma>') `` {v} \<noteq> {}" by fast
      qed
      subgoal by (rule V\<^sub>0_in_V)
      done
    from Ginter.finite_graph_always_has_cycle_from_node[OF \<open>v\<in>V\<close>] Ginter.succ \<open>v\<in>V\<close>
    obtain xs where xs: "cycle_from_node (G\<sigma> \<inter> G\<sigma>') v xs" by blast
    moreover from xs have "cycle_from_node G\<sigma> v xs" using cycle_from_node_inter_1 by fastforce
    with \<sigma>_win have "winningP (top_priority xs)" by blast
    moreover from xs have "cycle_from_node G\<sigma>' v xs" using cycle_from_node_inter_2 by fastforce
    ultimately show "\<exists>xs. cycle_from_node (G\<sigma>') v xs \<and> winning_player xs" by blast
  qed

  corollary "\<not>(won_by_player v \<and> won_by_opponent v)" using w1 by blast
end

term "player_arena.won_by_player E V prio V\<^sub>\<alpha> winningP"

lemma card_induct[consumes 1, case_names less]:
  fixes V :: "'a set"
  assumes FIN: "finite V"
  assumes STEP: "\<And>V. \<lbrakk> \<And>V'. \<lbrakk> finite V'; card V' < card V \<rbrakk> \<Longrightarrow> P V' \<rbrakk> \<Longrightarrow> P V"
  shows "P V"
proof -

  have "wf (measure card)" by simp
  then show "P V" using FIN
    apply (induction rule: wf_induct_rule)
    apply simp using STEP .

qed

context finite_graph_V begin
  lemma restrict_graph:
    assumes "V' \<subseteq> V"
    assumes "E' \<subseteq> ((E\<union>Id) \<inter> V'\<times>V')"
    assumes succ: "\<And>v. v\<in>V' \<Longrightarrow> E'``{v}\<noteq>{}"
    shows "finite_graph_V E' V'"
    using assms apply unfold_locales
    by (auto dest: finite_subset)

end

context arena_defs begin

  lemma restrict_arena:
    assumes "V' \<subseteq> V"
    assumes "E' \<subseteq> ((E\<union>Id) \<inter> V'\<times>V')"
    assumes succ: "\<And>v. v\<in>V' \<Longrightarrow> E'``{v}\<noteq>{}"
    assumes "V\<^sub>0' \<subseteq> V'"
    shows "arena_defs E' V' V\<^sub>0'"
    apply intro_locales
    using restrict_graph[OF assms(1,2,3)] apply blast
    apply unfold_locales
    by fact

end

context player_arena begin
  lemma restrict_player_arena:
    assumes "V' \<subseteq> V"
    assumes "E' \<subseteq> ((E\<union>Id) \<inter> V'\<times>V')"
    assumes succ: "\<And>v. v\<in>V' \<Longrightarrow> E'``{v}\<noteq>{}"
    assumes "V\<^sub>0' \<subseteq> V'"
    assumes "V\<^sub>\<alpha>' \<subseteq> V'"
    shows "player_arena E' V' V\<^sub>0' V\<^sub>\<alpha>'"
    apply intro_locales
    using restrict_graph[OF assms(1,2,3)] apply blast
    apply unfold_locales
    by fact+

end


datatype player = EVEN | ODD

fun opponent where
  "opponent EVEN = ODD"
| "opponent ODD = EVEN"

lemma opponent2[simp]: "opponent (opponent p) = p"
  by (cases p) auto


context arena_defs begin

  sublocale P0: player_arena E V V\<^sub>0 prio V\<^sub>0 even
    apply unfold_locales
    by (rule V\<^sub>0_in_V)

  sublocale P1: player_arena E V V\<^sub>0 prio V\<^sub>1 odd
    apply unfold_locales
    by (rule V\<^sub>1_in_V)

  fun V_player where
    "V_player EVEN = V\<^sub>0"
  | "V_player ODD = V\<^sub>1"

  fun attractor where
    "attractor EVEN = P0.attractor"
  | "attractor ODD = P1.attractor"

  fun won_by where
    "won_by EVEN = P0.won_by_player"
  | "won_by ODD = P1.won_by_player"

  lemma V_diff_diff_V0: "(V - (V - V\<^sub>0)) = V\<^sub>0"
    by (simp add: V\<^sub>0_in_V double_diff)

  lemma won_by_opponent_simps[simp]:
    "P1.won_by_opponent = P0.won_by_player"
    "P0.won_by_opponent = P1.won_by_player"
    unfolding P0.won_by_opponent_def P1.won_by_opponent_def P0.won_by_player_def P1.won_by_player_def
    unfolding V\<^sub>1_def
    by (auto simp: V_diff_diff_V0)

  term P0.attractor
  term P1.attractor
end

lemma mark: "False" (* Just to mark where the most recent proof attempt begins *) oops

lemma aux:
  fixes v :: 'v
  assumes player_arena: "player_arena E V V\<^sub>0 V\<^sub>\<alpha>"
  assumes "v\<in>V"
  shows "player_arena.won_by_player E V prio V\<^sub>\<alpha> winningP v \<or> player_arena.won_by_opponent E V prio V\<^sub>\<alpha> winningP v"
proof -
  have "finite V" proof -
    interpret player_arena E V V\<^sub>0 prio V\<^sub>\<alpha> winningP by fact
    show ?thesis by blast
  qed
  then show ?thesis using assms
  proof (induction arbitrary: E V\<^sub>0 V\<^sub>\<alpha> v rule: card_induct)
    case (less V)

    interpret player_arena E V V\<^sub>0 prio V\<^sub>\<alpha> winningP by fact

    (* Maybe we can construct a smaller graph by following the proof sketched by Tom *)
    (* The highest priority in V *)
    define p :: "nat" where "p = (MAX v' \<in> V. prio v')"
    (* Some vertex of that highest priority *)
    define v' :: "'v" where "v' =(SOME w. w \<in> V \<and> prio w = p)"
    (* Attract to that v' for the player that wins p.
       In the context of player_arena, this is not possible!
       We can only attract for the player that owns V\<^sub>\<alpha>, which might not be the one who wins p!*)
    define A :: "'v set" where  "A = attractor {v'}"

    (* My first attempt to just construct something without thinking about specifics: removing v from the graph *)
    define E' :: "'v rel" where "E'=E-(UNIV \<times> {v} \<union> {v} \<times> UNIV)"
    define V' :: "'v set" where "V'=V-{v}"
    define V\<^sub>0' :: "'v set" where "V\<^sub>0'=V\<^sub>0-{v}"
    define V\<^sub>\<alpha>' :: "'v set" where "V\<^sub>\<alpha>'=V\<^sub>\<alpha>-{v}"

    have ARENA': "player_arena E' V' V\<^sub>0' V\<^sub>\<alpha>'" and FIN: "finite V'" and LESS: "card V' < card V"
      unfolding E'_def V'_def V\<^sub>0'_def V\<^sub>\<alpha>'_def
      apply unfold_locales
      apply simp_all
        subgoal using E_in_V by blast
        subgoal for v' sorry (* constructing the new graph by just removing v does not ensure successors *)
        subgoal using V\<^sub>0_in_V by blast
        subgoal using V\<^sub>\<alpha>_subset by blast
        subgoal using less.prems(2) psubset_card_mono[OF fin_V] by force
        done

    interpret subgame: player_arena E' V' V\<^sub>0' prio V\<^sub>\<alpha>' winningP
      using ARENA' by auto

    note IH = less.IH[OF FIN LESS ARENA']
    show "won_by_player v \<or> won_by_opponent v" sorry
  qed
qed

context player_arena begin

  lemma "v\<in>V \<Longrightarrow> won_by_player v \<or> won_by_opponent v"
    using aux player_arena_axioms by metis

end

context arena_defs
begin
  (* how do I bring attractors into a context where the player is not fixed? *)
  abbreviation "attr_even \<equiv> attractor V\<^sub>0"
  abbreviation "attr_odd \<equiv> attractor V\<^sub>1"

  thm attract_strategy[where V\<^sub>\<alpha>=V\<^sub>0]
  thm attract_strategy[where V\<^sub>\<alpha>=V\<^sub>1]

  definition won_by_even :: "'v \<Rightarrow> bool" where
    "won_by_even v \<equiv> v\<in>V \<and> (\<exists>\<sigma>. strategy_of V\<^sub>0 \<sigma> \<and>
    (\<forall>xs. cycle_from_node (induced_by_strategy (dom \<sigma>) \<sigma>) v xs \<longrightarrow> winning_even xs))"

  lemma "won_by_even v \<Longrightarrow> (\<exists>\<sigma>. strategy_of V\<^sub>0 \<sigma> \<and>
    (\<forall>xs. cycle_from_node (induced_by_strategy (dom \<sigma>) \<sigma>) v xs \<longrightarrow> \<not>winning_odd xs))"
    unfolding won_by_even_def by auto

  definition won_by_odd :: "'v \<Rightarrow> bool" where
    "won_by_odd v \<equiv> v\<in>V \<and> (\<exists>\<sigma>. strategy_of V\<^sub>1 \<sigma> \<and>
    (\<forall>xs. cycle_from_node (induced_by_strategy (dom \<sigma>) \<sigma>) v xs \<longrightarrow> winning_odd xs))"

  lemma "won_by_odd v \<Longrightarrow> \<exists>\<sigma>. strategy_of V\<^sub>1 \<sigma> \<and>
    (\<forall>xs. cycle_from_node (induced_by_strategy (dom \<sigma>) \<sigma>) v xs \<longrightarrow> \<not>winning_even xs)"
    unfolding won_by_odd_def by auto

  lemma V\<^sub>0_induced_succs_1: "v\<in>V\<^sub>0 \<Longrightarrow> strategy_of V\<^sub>1 \<sigma>' \<Longrightarrow> induced_by_strategy (dom \<sigma>') \<sigma>' `` {v} = E `` {v}"
    unfolding induced_by_strategy_def E_of_strat_def strategy_of_def V\<^sub>1_def by auto

  lemma V\<^sub>0_induced_succs_2: "v\<in>V\<^sub>0 \<Longrightarrow> strategy_of V\<^sub>0 \<sigma> \<Longrightarrow> induced_by_strategy (dom \<sigma>) \<sigma> `` {v} \<noteq> {}"
    unfolding induced_by_strategy_def E_of_strat_def strategy_of_def
    using succ[of v] V\<^sub>0_in_V
    apply (cases "v\<in>dom \<sigma>")
    subgoal by auto
    subgoal by blast
    done

  lemma V\<^sub>1_induced_succs_1: "v\<in>V\<^sub>1 \<Longrightarrow> strategy_of V\<^sub>0 \<sigma>' \<Longrightarrow> induced_by_strategy (dom \<sigma>') \<sigma>' `` {v} = E `` {v}"
    unfolding induced_by_strategy_def E_of_strat_def strategy_of_def V\<^sub>1_def by auto

  lemma V\<^sub>1_induced_succs_2: "v\<in>V\<^sub>1 \<Longrightarrow> strategy_of V\<^sub>1 \<sigma> \<Longrightarrow> induced_by_strategy (dom \<sigma>) \<sigma> `` {v} \<noteq> {}"
    unfolding induced_by_strategy_def E_of_strat_def strategy_of_def V\<^sub>1_def
    using succ[of v] apply (cases "v\<in>dom \<sigma>") by auto

  lemma w1: "won_by_even v \<Longrightarrow> \<not>won_by_odd v"
    unfolding won_by_even_def won_by_odd_def
  proof clarsimp
    fix \<sigma> \<sigma>'
    define G\<sigma> where "G\<sigma> = induced_by_strategy (dom \<sigma>) \<sigma>"
    define G\<sigma>' where "G\<sigma>' = induced_by_strategy (dom \<sigma>') \<sigma>'"
    assume \<sigma>_even: "strategy_of V\<^sub>0 \<sigma>"
      and \<sigma>_win: "\<forall>xs. cycle_from_node G\<sigma> v xs \<longrightarrow> even (top_priority xs)"
      and \<sigma>'_odd: "strategy_of V\<^sub>1 \<sigma>'"
      and "v\<in>V"
    interpret Ginter: arena_defs "G\<sigma> \<inter> G\<sigma>'" V V\<^sub>0 prio
      apply unfold_locales
      subgoal unfolding G\<sigma>_def using ind_subgraph E_in_V by blast
      subgoal by simp
      subgoal proof cases
        fix v
        assume v_in_V\<^sub>0: "v\<in>V\<^sub>0"
        with \<sigma>'_odd have "G\<sigma>' `` {v} = E `` {v}"
          unfolding G\<sigma>'_def by (simp add: V\<^sub>0_induced_succs_1)
        moreover from v_in_V\<^sub>0 \<sigma>_even have "G\<sigma> `` {v} \<noteq> {}"
          unfolding G\<sigma>_def by (simp add: V\<^sub>0_induced_succs_2)
        moreover note succ[of v]
        moreover have "G\<sigma> \<subseteq> E" using ind_subgraph E_in_V by (simp add: G\<sigma>_def)
        ultimately show "(G\<sigma> \<inter> G\<sigma>') `` {v} \<noteq> {}" by fast
      next
        fix v
        assume "v\<in>V" "v\<notin>V\<^sub>0"
        hence v_in_V\<^sub>1: "v\<in>V\<^sub>1" unfolding V\<^sub>1_def by auto
        with \<sigma>_even have "G\<sigma> `` {v} = E `` {v}"
          unfolding G\<sigma>_def by (simp add: V\<^sub>1_induced_succs_1)
        moreover from v_in_V\<^sub>1 \<sigma>'_odd have "G\<sigma>' `` {v} \<noteq> {}"
          unfolding G\<sigma>'_def by (simp add: V\<^sub>1_induced_succs_2)
        moreover note succ[of v]
        moreover have "G\<sigma>' \<subseteq> E" using ind_subgraph E_in_V by (simp add: G\<sigma>'_def)
        ultimately show "(G\<sigma> \<inter> G\<sigma>') `` {v} \<noteq> {}" by fast
      qed
      subgoal by (rule V\<^sub>0_in_V)
      done
    from Ginter.finite_graph_always_has_cycle_from_node[OF \<open>v\<in>V\<close>] Ginter.succ \<open>v\<in>V\<close>
    obtain xs where xs: "cycle_from_node (G\<sigma> \<inter> G\<sigma>') v xs" by blast
    moreover from xs have "cycle_from_node G\<sigma> v xs" using cycle_from_node_inter_1 by fastforce
    with \<sigma>_win have "even (top_priority xs)" by blast
    moreover from xs have "cycle_from_node G\<sigma>' v xs" using cycle_from_node_inter_2 by fastforce
    ultimately show "\<exists>xs. cycle_from_node (G\<sigma>') v xs \<and> even (top_priority xs)" by blast
  qed

  (*lemma w': "\<not>won_by_odd v \<Longrightarrow> won_by_even v" unfolding won_by_odd_def won_by_even_def apply clarsimp
  apply (drule spec[where x=\<sigma>1]) apply (subgoal_tac "strategy_of V\<^sub>1 \<sigma>1") apply clarsimp oops

  lemma w2:"won_by_even v \<or> won_by_odd v" oops

  lemma "won_by_even v \<noteq> won_by_odd v" (*using w1 w'*) oops
  *)


  lemma subarenaI:
    assumes "V'\<subseteq>V"
    assumes "\<And>v. v\<in>V' \<Longrightarrow> E``{v} \<inter> V' \<noteq> {}"
    shows "arena_defs (E \<inter> (V'\<times>V')) V' (V\<^sub>0 \<inter> V')"
    apply unfold_locales
    using assms succ
    by (auto intro: finite_subset)



end

  term "arena_defs.won_by_even E V V\<^sub>0 prio"

        find_theorems arg_max

(* TODO: this is a general lemma! *)
lemma obtain_max_arg_finite_set_nat:
  fixes f :: "'a \<Rightarrow> nat"
  assumes "finite S" "S\<noteq>{}"
  obtains s where "s\<in>S" "\<forall>s'\<in>S. f s' \<le> f s"
proof -
  have "\<exists>s\<in>S. \<forall>s'\<in>S. f s' \<le> f s"
    using assms
    apply (induction)
    apply auto
    by force
  thus ?thesis using that by blast
qed




(**
  lemma
    fixes E V V\<^sub>0 and prio :: "'v \<Rightarrow> nat"
    assumes "arena_defs E V V\<^sub>0"
    shows "\<exists>W\<^sub>0 W\<^sub>1. V = W\<^sub>0 \<union> W\<^sub>1 \<and> W\<^sub>0 \<inter> W\<^sub>1 = {} \<and> (\<forall>v\<in>W\<^sub>0. arena_defs.won_by_even E V V\<^sub>0 prio v) \<and> (\<forall>v\<in>W\<^sub>1. arena_defs.won_by_odd E V V\<^sub>0 prio v)"
  proof -
    have "finite V"
    proof -
      from assms interpret arena_defs E V V\<^sub>0 prio .
      show ?thesis by (rule fin_V)
    qed
    then show ?thesis using assms
    proof (induction arbitrary: E V\<^sub>0 rule: finite_psubset_induct)
      case (psubset V)

      interpret arena_defs E V V\<^sub>0 prio by fact

      show ?case proof (cases)
        assume "V={}"
        thus ?thesis by blast
      next
        assume "V\<noteq>{}"

        find_theorems arg_max_on

        find_theorems "_\<noteq>{}" "?a\<in>_" "_ \<le> ?f ?a"

        find_theorems "arg_max_on"

        obtain v where V_NODE: "v\<in>V" and V_MAXP: "\<forall>v'\<in>V. prio v' \<le> prio v"
          using obtain_max_arg_finite_set_nat[OF _ \<open>V\<noteq>{}\<close>, of prio] by blast

        assume WLOG_EVEN: "even (prio v)"

        define A where "A = attr_even "


      then show ?case sorry
    qed *)
end
