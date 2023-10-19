theory Digraphs
imports Main
begin
(** This file contains general definitions for directed graphs, paths, lassos, and cycles. *)

chapter \<open>Directed Graphs\<close>
type_synonym 'v dgraph = "'v rel"

(** EV is used as shorthand for getting all nodes in the directed graph. *)
abbreviation EV :: "'v dgraph \<Rightarrow> 'v set" where
  "EV E \<equiv> fst ` E \<union> snd ` E"


section \<open>Strongly Connected Components\<close>
(** A graph is strongly connected if every pair of vertices v,v' in V, there exists a path from
    v to v' and vice-versa. We do not need to specify both directions, because this follows from
    the definition automatically. *)
definition strongly_connected :: "'v dgraph \<Rightarrow> bool" where
 "strongly_connected E \<equiv> \<forall>v \<in> EV E. \<forall>v' \<in> EV E. (v,v') \<in> E\<^sup>*"

context
  fixes E :: "'v dgraph"
begin
(** In a context where a graph is fixed already, we can say a component of it is strongly connected
    if the graph restricted to that component is strongly connected. *)
definition SCC :: "'v set \<Rightarrow> bool" where
  "SCC S \<equiv> S \<subseteq> EV E \<and> strongly_connected (E \<inter> S\<times>S)"


section \<open>Paths\<close>
(** A path as a list of the first node of each edge that path in a graph. *)
fun path :: "'v \<Rightarrow> 'v list \<Rightarrow> 'v \<Rightarrow> bool" where
  "path v [] v' \<longleftrightarrow> v = v'"
| "path v (x#xs) v' \<longleftrightarrow> (\<exists>y. x=v \<and> (v,y) \<in> E \<and> path y xs v')"

(** A path can be composed of multiple paths. *)
lemma path_append[simp]: "path u (xs\<^sub>1@xs\<^sub>2) v \<longleftrightarrow> (\<exists>u'. path u xs\<^sub>1 u' \<and> path u' xs\<^sub>2 v)"
  by (induction xs\<^sub>1 arbitrary: u) auto

(** The path is equivalent tot eh reflexive transitive closure in the graph. We prove both
    directions separately before proving the equivalence using those lemmas. *)
lemma path_is_rtrancl: "path v xs v' \<Longrightarrow> (v,v')\<in>E\<^sup>*"
  by (induction xs arbitrary: v) fastforce+

lemma rtrancl_is_path: "(v,v')\<in>E\<^sup>* \<Longrightarrow> \<exists>xs. path v xs v'"
  apply (induction rule: converse_rtrancl_induct)
  using path.simps by blast+

lemma path_iff_rtrancl: "(v,v') \<in> E\<^sup>* \<longleftrightarrow> (\<exists>xs. path v xs v')"
  using rtrancl_is_path path_is_rtrancl by auto

(** The nodes in a path are in the graph. *)
lemma path_in_E: "path v xs v' \<Longrightarrow> set xs \<subseteq> EV E"
proof (induction xs arbitrary: v)
  case Nil thus ?case by simp
next
  case (Cons a xs)
  hence "v = a" by auto
  moreover from this Cons have "\<exists>y. (v,y)\<in>E" by auto
  ultimately have "a \<in> fst ` E" by force
  with Cons show ?case by auto
qed

(** The origin of a path is included in its set of nodes. *)
lemma origin_in_path: "\<lbrakk>path v xs v'; xs \<noteq> []\<rbrakk> \<Longrightarrow> v \<in> set xs"
  by (cases xs) auto

(** A path can be deconstructed into its first edge and the rest of the path. *)
lemma path_D: "\<lbrakk>path v xs v'; xs \<noteq> []\<rbrakk> \<Longrightarrow> \<exists>y ys. xs = v#(ys) \<and> (v,y) \<in> E \<and> path y ys v'"
  by (induction xs arbitrary: v) auto

(** If a path is in a closed region of a graph, its nodes will entirely be in that region *)
lemma path_closed_set: "\<lbrakk>v\<in>V; E``V\<subseteq>V; path v xs v'\<rbrakk> \<Longrightarrow> set xs \<subseteq> V"
  apply (induction xs arbitrary: v) by auto

(** If a path is in a closed region of a graph, its destination will be in that region. *)
lemma path_closed_dest: "\<lbrakk>v\<in>V; E``V\<subseteq>V; path v xs v'\<rbrakk> \<Longrightarrow> v'\<in>V"
  apply (induction xs arbitrary: v) by auto

(** If a path is in a partially closed region of a graph, and it does not move through the area
    excluded in closedness, its nodes are entirely in the region minus that area. *)
lemma path_partially_closed_set: "\<lbrakk>v\<in>V-R; E``(V-R)\<subseteq>V; path v xs v'; set xs \<inter> R = {}\<rbrakk>
  \<Longrightarrow> set xs \<subseteq> V-R"
  apply (induction xs arbitrary: v; simp)
    subgoal for x xs by (cases xs) auto
  done

(** If a path is in a partially closed region of a graph, and it does not move through the area
    excluded in closedness, is destination is within the partially closed region. *)
lemma path_partially_closed_dest: "\<lbrakk>v\<in>V-R; E``(V-R)\<subseteq>V; path v xs v'; set xs \<inter> R = {}\<rbrakk> \<Longrightarrow> v'\<in>V"
  apply (induction xs arbitrary: v; simp)
    subgoal for x xs by (cases xs) auto
  done

(** If you have an intermediate node in a path, you can split it into two paths with the
    intermediate node in the middle. *)
lemma path_intermediate_node: "\<lbrakk>path v xs v'; x \<in> set xs\<rbrakk>
  \<Longrightarrow> \<exists>xs1 xs2. xs = (xs1@xs2) \<and> path v xs1 x \<and> path x xs2 v'"
  apply (induction xs arbitrary: v)
    subgoal by simp
    subgoal for x' xs using split_list_first[of x "x'#xs"] by fastforce
  done


section \<open>Cycles\<close>
(** A cycle from a node to itself. *)
definition cycle :: "'v \<Rightarrow> 'v list \<Rightarrow> bool" where
  "cycle v xs \<equiv> path v xs v \<and> xs \<noteq> []"

lemma cycle_not_empty[simp]:"\<not>cycle v []"
  unfolding cycle_def by auto

(** The origin of a cycle is part of the cycle. *)
lemma origin_in_cycle: "cycle x xs \<Longrightarrow> x \<in> set xs"
  unfolding cycle_def using origin_in_path by blast

(** The nodes in a cycle exist in the graph. *)
lemma cycle_in_E: "cycle x xs \<Longrightarrow> set xs \<subseteq> EV E"
  unfolding cycle_def using path_in_E by blast

(** A cycle can be deconstructed into its first edge and a cycle from that edge's target. *)
lemma cycle_D: "cycle x xs \<Longrightarrow> \<exists>y ys. xs=x#ys \<and> set (ys@[x]) = set xs \<and> (x,y)\<in>E \<and> y\<in>set xs \<and> cycle y (ys@[x])"
  unfolding cycle_def
  using origin_in_path
  by (induction xs; simp) force

(** If a cycle is in a closed region of a graph, its nodes are all in that region. *)
lemma cycle_closed_set: "\<lbrakk>v\<in>V; E``V\<subseteq>V; cycle v xs\<rbrakk> \<Longrightarrow> set xs \<subseteq> V"
  unfolding cycle_def using path_closed_set by blast

(** If a cycle is in a partially closed region of a graph, and it does not move through the area
  excluded in closedness, its nodes are entirely in the region minus that area. *)
lemma cycle_partially_closed_set: "\<lbrakk>v\<in>V-R; E``(V-R)\<subseteq>V; cycle v xs; set xs \<inter> R = {}\<rbrakk>
    \<Longrightarrow> set xs \<subseteq> V-R"
  unfolding cycle_def using path_partially_closed_set by blast

(** If you have a looping path and an intermediate node in that path, you can get another looping
    path from that intermediate node to itself. *)
lemma loop_intermediate_node: "\<lbrakk>path v vs v; x \<in> set vs\<rbrakk> \<Longrightarrow> \<exists>vs'. set vs' = set vs \<and> path x vs' x"
proof -
  assume path_v_vs_v: "path v vs v" and x_in_vs: "x \<in> set vs"
  (** We can split the path into two paths from v to x and from x to v. *)
  from path_intermediate_node[OF path_v_vs_v x_in_vs] obtain vs1 vs2 where
    vs_concat: "vs = vs1@vs2" and
    vs1_to_x: "path v vs1 x" and
    vs2_to_v: "path x vs2 v" by blast
  (** Now, we can append those paths to form a loop again. *)
  hence "path x (vs2@vs1) x" by auto
  moreover from vs_concat have "set (vs2@vs1) = set vs" by force
  ultimately show ?thesis by blast
qed

(** A cycle is a nonempty path looping on itself. *)
lemma cycle_iff_loop:  "cycle v vs \<longleftrightarrow> path v vs v \<and> vs \<noteq> []"
  unfolding cycle_def by blast

(** If you have a cycle and an intermediate node in that cycle, you can get another cycle from
    that intermediate node. *)
lemma cycle_intermediate_node:
  "\<lbrakk>cycle v vs; x \<in> set vs\<rbrakk> \<Longrightarrow> \<exists>vs'. set vs' = set vs \<and> cycle x vs'"
  using cycle_iff_loop loop_intermediate_node[of v vs x] by fastforce


section \<open>Reachable cycles\<close>
 (** A cycle reachable from a node. *)
definition cycle_from_node :: "'v \<Rightarrow> 'v list \<Rightarrow> bool" where
  "cycle_from_node x ys \<equiv> \<exists>xs y. path x xs y \<and> cycle y ys"

lemma cycle_from_node_not_empty[simp]: "\<not>cycle_from_node v []"
  unfolding cycle_from_node_def by auto

(** The nodes in a cycle are in the graph. *)
lemma cycle_from_node_in_E: "cycle_from_node v ys \<Longrightarrow> set ys \<subseteq> EV E"
  unfolding cycle_from_node_def
  using path_in_E cycle_in_E by blast

(** A cycle from a node is equivalent to two paths existing from x to some y, and from y to itself. *)
lemma cycle_from_node_paths:
  "cycle_from_node x ys \<longleftrightarrow> (\<exists>xs y. path x xs y \<and> path y ys y \<and> ys \<noteq> [])"
  unfolding cycle_from_node_def cycle_def by simp

(** A cycle from a node implies the existence of a single path from x to some y at the start of the
    loop. *)
lemma cycle_from_node_impl_path: "cycle_from_node x ys \<Longrightarrow> \<exists>vs y. path x vs y"
  using cycle_from_node_paths by auto

(** If a cycle from a node is in a closed region of a graph, its nodes are in that closed region. *)
lemma cycle_from_node_closed_set: "\<lbrakk>x\<in>V; E``V\<subseteq>V; cycle_from_node x ys\<rbrakk> \<Longrightarrow> set ys \<subseteq> V"
  using cycle_from_node_paths path_closed_dest path_closed_set by meson

(** If there exists a cycle reachable from x, then that is a cycle reachable from its own starting
    point. *)
lemma cycle_from_node_loop: "cycle_from_node x ys \<Longrightarrow> \<exists>y\<in>set ys. cycle_from_node y ys"
  unfolding cycle_from_node_def cycle_def
  using origin_in_path by blast

(** If a nonempty loop exists, then that is a cycle reachable from its start. *)
lemma loop_impl_cycle_from_node: "path v vs v \<and> vs \<noteq> [] \<Longrightarrow> cycle_from_node v vs"
  unfolding cycle_from_node_def cycle_def by blast

(** If a cycle exists, then that is a cycle reachable from its own start. *)
lemma cycle_impl_cycle_from_node: "cycle v vs \<Longrightarrow> cycle_from_node v vs"
  unfolding cycle_from_node_def cycle_def by blast


section \<open>Lassos\<close>
(** A lasso from a node with a spoke and a loop. *)
definition lasso_from_node :: "'v \<Rightarrow> 'v list \<Rightarrow> 'v list \<Rightarrow> bool" where
  "lasso_from_node x xs ys \<equiv> \<exists>y. path x xs y \<and> cycle y ys"

lemma lasso_from_node_not_empty[simp]:"\<not>lasso_from_node x xs []"
  unfolding lasso_from_node_def by auto

(** The nodes in the lasso are in the graph. *)
lemma lasso_from_node_in_E: "lasso_from_node x xs ys
  \<Longrightarrow> set xs \<subseteq> (EV E) \<and> set ys \<subseteq> (EV E)"
  unfolding lasso_from_node_def
  using path_in_E cycle_in_E by force

(** The origin of a lasso is somewhere in the lasso, either in the spoke, or in the loop if the
    spoke is empty. *)
lemma origin_in_lasso: "lasso_from_node x xs ys \<Longrightarrow> (x \<in> set xs \<or> x \<in> set ys)"
  unfolding lasso_from_node_def cycle_def
  using path.simps origin_in_path by metis

(** A lasso is equivalent to two paths; a spoke and a loop. *)
lemma lasso_from_node_paths:
  "lasso_from_node x xs ys \<longleftrightarrow> (\<exists>y. path x xs y \<and> path y ys y \<and> ys \<noteq> [])"
  unfolding lasso_from_node_def cycle_def by simp

(** If we have a lasso, we have a single path covering the spoke and loop, terminating at the start
    of the loop. *)
lemma lasso_from_node_impl_path:
  "lasso_from_node x xs ys \<Longrightarrow> \<exists>y vs. vs = xs@ys \<and> y \<in> set vs \<and> path x vs y"
  unfolding lasso_from_node_def cycle_def
  using path_append origin_in_path by auto

(** If a lasso is in a closed region of a graph, its nodes are in that region. *)
lemma lasso_from_node_closed_sets: "\<lbrakk>x\<in>V; E``V\<subseteq>V; lasso_from_node x xs ys\<rbrakk> \<Longrightarrow> set xs \<subseteq> V \<and> set ys \<subseteq> V"
  using lasso_from_node_paths path_closed_dest[of x V xs] path_closed_set[of _ V] by metis

(** If a lasso is in a partially closed region of a graph, and it does not go through the part of
    the region where it can exit, it will stay in the region. *)
lemma lasso_from_node_partially_closed_sets:
  assumes "x\<in>V-R"
  assumes "E``(V-R)\<subseteq>V"
  assumes "set xs \<inter> R = {}"
  assumes "set ys \<inter> R = {}"
  assumes "lasso_from_node x xs ys"
  shows "set xs \<subseteq> V-R \<and> set ys \<subseteq> V-R"
proof -
  from assms(5) obtain y where
    path_x_xs_y: "path x xs y" and
    cycle_y_ys: "cycle y ys"
    unfolding lasso_from_node_def by blast

  from path_partially_closed_set[OF assms(1,2) path_x_xs_y assms(3)]
  have xs_in_V_min_R: "set xs \<subseteq> V-R" .

  from path_partially_closed_dest[OF assms(1,2) path_x_xs_y assms(3)] assms(4)
  have "y \<in> V-R" using origin_in_cycle[OF cycle_y_ys] by blast
  from cycle_partially_closed_set[OF this assms(2) cycle_y_ys assms(4)]
  have ys_in_V_min_R: "set ys \<subseteq> V-R" .

  from xs_in_V_min_R ys_in_V_min_R show ?thesis ..
qed

(** If we have a lasso, then there exists a y at the start of the loop, from which there is a lasso
    without a spoke. *)
lemma lasso_from_node_loop:
  "lasso_from_node x xs ys \<Longrightarrow> \<exists>y. y \<in> set ys \<and> lasso_from_node y [] ys"
  unfolding lasso_from_node_def cycle_def
  using origin_in_path by auto

(** If there is a looping path from y, there is a lasso from y without a spoke. *)
lemma loop_impl_lasso: "\<lbrakk>path y ys y; ys \<noteq> []\<rbrakk> \<Longrightarrow> lasso_from_node y [] ys"
  unfolding lasso_from_node_def cycle_def by simp

(** A cycle is a lasso without a spoke. *)
lemma cycle_iff_lasso: "cycle y ys \<longleftrightarrow> lasso_from_node y [] ys"
  unfolding lasso_from_node_def by simp

(** If there is a cycle, it means there is a lasso, and vice versa. *)
lemma cycle_from_iff_lasso: "cycle_from_node x ys \<longleftrightarrow> (\<exists>xs. lasso_from_node x xs ys)"
  unfolding lasso_from_node_def cycle_from_node_def by simp

(** A lasso from a node with spoke and loop in a single list. *)
definition lasso_from_node' :: "'v \<Rightarrow> 'v list \<Rightarrow> bool" where
  "lasso_from_node' x vs \<equiv> \<exists>y xs ys. vs=xs@ys \<and>  path x xs y \<and> cycle y ys"

lemma lasso_from_node'_not_empty[simp]: "\<not>lasso_from_node' v []"
  unfolding lasso_from_node'_def by simp

(** The length of a lasso is always greater than 0. *)
lemma lasso_from_node'_length: "lasso_from_node' v vs \<Longrightarrow> 0 < length vs"
  by force

(** The nodes in a lasso are in the graph. *)
lemma lasso_from_node'_in_E: "lasso_from_node' x vs \<Longrightarrow> set vs \<subseteq> (EV E)"
  unfolding lasso_from_node'_def cycle_def
  using path_append path_in_E by blast

(** The origin of a lasso is in its nodes. *)
lemma origin_in_lasso': "lasso_from_node' x vs \<Longrightarrow> x \<in> set vs"
  unfolding lasso_from_node'_def cycle_def
  using path_append origin_in_path by blast

(** A lasso is equivalent to two paths; a spoke and a loop. *)
lemma lasso_from_node'_paths:
  "lasso_from_node' x vs \<longleftrightarrow> (\<exists>y xs ys. vs=xs@ys \<and> path x xs y \<and> path y ys y \<and> ys \<noteq> [])"
  unfolding lasso_from_node'_def cycle_def by simp

(** If a lasso is in a closed region of a graph, its nodes are also in that region. *)
lemma lasso_from_node'_closed_set: "\<lbrakk>x\<in>V; E``V\<subseteq>V; lasso_from_node' x vs\<rbrakk> \<Longrightarrow> set vs \<subseteq> V"
proof -
  assume x_in_V: "x\<in>V" and E_closed_V: "E``V\<subseteq>V" and lasso'_x_vs: "lasso_from_node' x vs"
  from lasso'_x_vs obtain xs y ys where
    vs_comp: "vs=xs@ys" and
    path_x_xs_y: "path x xs y" and
    path_y_ys_y: "path y ys y"
    using lasso_from_node'_paths by auto
  from x_in_V E_closed_V path_x_xs_y have xs_in_V: "set xs \<subseteq> V" using path_closed_set by simp
  from x_in_V E_closed_V path_x_xs_y have y_in_V: "y\<in>V" using path_closed_dest by blast
  from y_in_V E_closed_V path_y_ys_y have ys_in_V: "set ys \<subseteq> V" using path_closed_set by simp
  from vs_comp xs_in_V ys_in_V show ?thesis by simp
qed

(** If there is a lasso, then there is a single path over the spoke and loop, terminating at the
    start of the loop. *)
lemma lasso'_impl_path: "lasso_from_node' x vs \<Longrightarrow> \<exists>y. y \<in> set vs \<and> path x vs y"
  unfolding lasso_from_node'_def cycle_def
  using path_append origin_in_path by fastforce

(** If there exists a loop, then that is a lasso reachable from its starting point. *)
lemma loop_impl_lasso': "\<lbrakk>path v vs v; vs \<noteq> []\<rbrakk> \<Longrightarrow> lasso_from_node' v vs"
  unfolding lasso_from_node'_def cycle_def by fastforce

(** If there is a cycle, then that is a lasso reachable from its starting point. *)
lemma cycle_impl_lasso': "cycle v vs \<Longrightarrow> lasso_from_node' v vs"
  unfolding lasso_from_node'_def cycle_def by fastforce

(** The two lassos are equivalent. *)
lemma lassos_equiv: "lasso_from_node' v xs \<longleftrightarrow> (\<exists>xs1 xs2. xs=xs1@xs2 \<and> lasso_from_node v xs1 xs2)"
  unfolding lasso_from_node'_def lasso_from_node_def cycle_def by auto

(** A lasso can be extended by appending its loop to the end. *)
lemma lasso'_extend_loop: "lasso_from_node' x vs \<Longrightarrow>
  \<exists>vs'. length vs < length vs' \<and> set vs = set vs' \<and> lasso_from_node' x vs'"
proof -
  assume lasso: "lasso_from_node' x vs"
  then obtain y xs ys where
    vs_decomp: "vs=xs@ys" and
    path_x_xs_y: "path x xs y" and
    path_y_ys_y: "path y ys y" and
    ys_notempty: "ys\<noteq>[]"
    using lasso_from_node'_paths by auto
  let ?vs' = "xs@ys@ys"
  show ?thesis
  proof (rule exI[where x="?vs'"]; intro conjI)
    from vs_decomp ys_notempty show "length vs < length ?vs'" by simp
    from vs_decomp show "set vs = set ?vs'" by simp
    from path_x_xs_y path_y_ys_y ys_notempty show "lasso_from_node' x ?vs'"
      unfolding lasso_from_node'_def cycle_def by fastforce
  qed
qed

(** A lasso can be extended to any length. *)
lemma lasso'_extend_any_length: "lasso_from_node' v vs
  \<Longrightarrow> \<exists>vs'. n < length vs' \<and> set vs = set vs' \<and> lasso_from_node' v vs'"
  apply (induction n)
    subgoal using lasso_from_node'_length by blast
    subgoal for n using lasso'_extend_loop Suc_lessI[of n] by metis
  done
end (** End of context with fixed E. *)


section \<open>Digraphs with Specific V and no Dead Ends\<close>
locale finite_graph_V_Succ =
  fixes E :: "'v dgraph"
  fixes V :: "'v set"
  assumes E_in_V: "E \<subseteq> V \<times> V"
  assumes fin_V[simp, intro]: "finite V"
  assumes succ: "v\<in>V \<Longrightarrow> E``{v}\<noteq>{}"
begin
(** E is finite. *)
lemma fin_E[simp, intro!]: "finite E"
  using E_in_V by (simp add: finite_subset)

(** E applied to any set ends up in a subset of V. *)
lemma E_closed_V: "E `` V' \<subseteq> V"
  using Image_subset[OF E_in_V] by simp

(** A path is closed in V. *)
lemma path_closed_V: "v\<in>V \<Longrightarrow> path E v xs v' \<Longrightarrow> v'\<in>V"
  using path_closed_dest[OF _ E_closed_V] by blast

(** All nodes in a path are in V. *)
lemma path_in_V: "\<lbrakk>v\<in>V; path E v xs v'\<rbrakk> \<Longrightarrow> set xs \<subseteq> V"
  using path_in_E E_in_V by fastforce

(** All nodes in a cycle are in V. *)
lemma cycle_in_V: "\<lbrakk>v\<in>V; cycle E v xs\<rbrakk> \<Longrightarrow> set xs \<subseteq> V"
  using cycle_in_E E_in_V by fastforce

lemma cycle_from_node_in_V: "\<lbrakk>v\<in>V; cycle_from_node E v xs\<rbrakk> \<Longrightarrow> set xs \<subseteq> V"
  using cycle_from_node_in_E E_in_V by fastforce

(** All nodes in a lasso reachable from a node are in V. *)
lemma lasso_from_node_in_V: "\<lbrakk>v\<in>V; lasso_from_node E v xs ys\<rbrakk> \<Longrightarrow> set xs \<subseteq> V \<and> set ys \<subseteq> V"
  using lasso_from_node_in_E E_in_V by fastforce

lemma lasso_from_node'_in_V: "\<lbrakk>v\<in>V; lasso_from_node' E v xs\<rbrakk> \<Longrightarrow> set xs \<subseteq> V"
  using lasso_from_node'_in_E E_in_V by fastforce

(** You can obtain a path of any desired length in the graph. *)
lemma path_any_length: "v\<in>V \<Longrightarrow> \<exists>xs v'. length xs = n \<and> path E v xs v'"
proof (induction n)
  case 0
  then obtain xs v' where "xs=([]::'v list)" and "v' = v" by simp
  thus ?case by auto
next
  case (Suc n)
  then obtain xs v' where path: "length xs = n" "path E v xs v'" by auto
  (** We can get a successor of the end of the path *)
  from path_closed_V[OF \<open>v\<in>V\<close> path(2)] Suc succ obtain w where succ: "w \<in> E``{v'}" by blast
  (** Then, we can extend the path to move to that successor, which makes it longer than the
      original path.*)
  then obtain ys where append: "ys = xs@[v']" by fast
  with path have length: "length ys = Suc n" by simp
  from append path succ have "path E v ys w" by auto
  with length show ?case by auto
qed

(** You can always get a cycle in a finite graph where every node has a successor. *)
lemma cycle_always_exists: "x\<in>V \<Longrightarrow> \<exists>xs. cycle_from_node E x xs"
proof -
  assume "x\<in>V"
  (** We can get a path of any length, so we get one that is longer than the number of nodes in V. *)
  then obtain xs x' where xs: "length xs = Suc (card V) \<and> path E x xs x'"
    using path_any_length by blast
  (** Since this path must be in V, it cannot have entirely distinct nodes in it; there must be a
      repeated node in there. *)
  have "\<not>distinct xs" proof -
    from xs have ss: "set xs \<subseteq> V" using path_in_V[OF \<open>x\<in>V\<close>] by fastforce
    from xs have len: "length xs > card V" by auto
    thus ?thesis using card_mono[OF fin_V ss] distinct_card[of xs] by fastforce
  qed
  (** Then we can get a node in the path that occurs in it twice, and split the path into three. *)
  then obtain y xs1 xs2 xs3 where decomp: "xs = xs1 @ [y] @ xs2 @ [y] @ xs3"
    using not_distinct_decomp by blast
  (** The first and second paths form a cycle reachable from x, completing the proof. *)
  with xs have "path E x (xs1) y" by auto
  moreover from decomp xs have "path E y (y#xs2) y" by auto
  ultimately have "cycle_from_node E x (y#xs2)" using cycle_from_node_paths by fast
  thus "\<exists>xs. cycle_from_node E x xs" by auto
qed

(** You can always get a lasso in a finite graph where every node has a successor. *)
lemma lasso_always_exists: "x\<in>V \<Longrightarrow> \<exists>xs ys. lasso_from_node E x xs ys"
  using cycle_always_exists cycle_from_iff_lasso[of E] by blast

lemma lasso'_always_exists: "x\<in>V \<Longrightarrow> \<exists>xs. lasso_from_node' E x xs"
  using lasso_always_exists lassos_equiv[of E] by simp
end (** End of locale finite_graph_V_Succ *)


section \<open>Subgraphs\<close>
(** If a path exists in a subgraph, it exists in the whole graph. *)
lemma subgraph_path: "E' \<subseteq> E \<Longrightarrow> path E' v vs v' \<Longrightarrow> path E v vs v'"
  apply (induction vs arbitrary: v) by auto

(** If a cycle exists in a subgraph, it exists in the whole graph. *)
lemma subgraph_cycle: "E' \<subseteq> E \<Longrightarrow> cycle E' v vs \<Longrightarrow> cycle E v vs"
  unfolding cycle_def
  by (simp add: subgraph_path)

lemma subgraph_cycle_from_node: "E' \<subseteq> E \<Longrightarrow> cycle_from_node E' v vs \<Longrightarrow> cycle_from_node E v vs"
  unfolding cycle_from_node_def using subgraph_path[of E' E] subgraph_cycle[of E' E] by fast

(** If a lasso exists in a subgraph, it exists in the whole graph. *)
lemma subgraph_lasso: "E' \<subseteq> E \<Longrightarrow> lasso_from_node E' v xs ys \<Longrightarrow> lasso_from_node E v xs ys"
  unfolding lasso_from_node_def using subgraph_path[of E' E] subgraph_cycle[of E' E] by fast

lemma subgraph_lasso': "E' \<subseteq> E \<Longrightarrow> lasso_from_node' E' v vs \<Longrightarrow> lasso_from_node' E v vs"
  using lassos_equiv[of E'] subgraph_lasso[of E' E] lassos_equiv[of E] by blast

(** If all nodes in a path exists in a region V, then it exists in the whole graph restricted to V. *)
lemma path_restr_V: "path E v vs v' \<Longrightarrow> set vs \<subseteq> V \<Longrightarrow> v' \<in> V \<Longrightarrow> path (E \<inter> V\<times>V) v vs v'"
  apply (induction vs arbitrary: v; simp)
  using origin_in_path by fastforce

lemma restr_V_path: "path (E \<inter> V\<times>V) v xs v' \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> v \<in> V \<and> set xs \<subseteq> V  \<and> path E v xs v'"
  apply (induction xs arbitrary: v; simp)
  using subgraph_path by force

(** If all nodes in a cycle exist in a region V, then it exists in the whole graph restricted to V. *)
lemma cycle_restr_V: "cycle E v xs \<Longrightarrow> set xs \<subseteq> V \<Longrightarrow> cycle (E \<inter> V\<times>V) v xs"
  unfolding cycle_def using path_restr_V[of E v xs v V] origin_in_path[of E v xs v] by fast

lemma restr_V_cycle: "cycle (E \<inter> V\<times>V) v xs \<Longrightarrow> set xs \<subseteq> V \<and> cycle E v xs"
  unfolding cycle_def using restr_V_path[of E V v xs v] by simp

(** If all nodes in a lasso exist in a region V, then it exists in the whole graph restricted to V. *)
lemma lasso_restr_V: "lasso_from_node E v xs ys \<Longrightarrow> set xs \<subseteq> V \<Longrightarrow> set ys \<subseteq> V \<Longrightarrow> lasso_from_node (E \<inter> V\<times>V) v xs ys"
  unfolding lasso_from_node_def cycle_def
  using path_restr_V[of E _ _ _ V] origin_in_path[of E] by blast

lemma restr_V_lasso: "lasso_from_node (E \<inter> V\<times>V) v xs ys \<Longrightarrow> set xs \<subseteq> V \<and> set ys \<subseteq> V \<and> lasso_from_node E v xs ys"
  unfolding lasso_from_node_def cycle_def
  using restr_V_path[of E V] set_append[of xs ys] set_empty[of xs] path.simps(1) empty_subsetI by metis

lemma lasso'_restr_V: "lasso_from_node' E v vs \<Longrightarrow> set vs \<subseteq> V \<Longrightarrow> lasso_from_node' (E \<inter> V\<times>V) v vs"
proof -
  assume lasso_v_vs: "lasso_from_node' E v vs" and
         vs_in_V: "set vs \<subseteq> V"

  from lasso_v_vs obtain xs v' ys where
    path_v_xs_v': "path E v xs v'" and
    path_v'_ys_v': "path E v' ys v'" and
    ys_notempty: "ys \<noteq> []" and vs_concat: "vs = xs@ys"
    using lasso_from_node'_paths[of E v vs] by fast

  from vs_in_V vs_concat have xs_in_V: "set xs \<subseteq> V" by simp
  from vs_in_V vs_concat have ys_in_V: "set ys \<subseteq> V" by simp
  from path_v'_ys_v' ys_in_V ys_notempty have v'_in_V: "v' \<in> V"
    using origin_in_path by fastforce

  from path_restr_V[OF path_v_xs_v' xs_in_V v'_in_V]
  have path_v_xs_v'_restr_V: "path (E \<inter> V\<times>V) v xs v'" .

  from path_restr_V[OF path_v'_ys_v' ys_in_V v'_in_V]
  have path_v'_ys_v'_restr_V: "path (E \<inter> V\<times>V) v' ys v'" .

  from path_v_xs_v'_restr_V path_v'_ys_v'_restr_V vs_concat ys_notempty
  show ?thesis
    using lasso_from_node'_def cycle_def by metis
qed

(** If a path exists in the intersection of two graphs, it exists in both of those graphs *)
lemma path_inter:
  "path (E \<inter> E') v vs v' \<Longrightarrow> path E v vs v'"
  "path (E \<inter> E') v vs v' \<Longrightarrow> path E' v vs v'"
  using inf_sup_ord(1,2)[of E E'] subgraph_path[of "E\<inter>E'"] by fast+

(** If a cycle exists in the intersection of two graphs, it exists in both of those graphs *)
lemma cycle_inter:
  "cycle (E \<inter> E') v vs \<Longrightarrow> cycle E v vs"
  "cycle (E \<inter> E') v vs \<Longrightarrow> cycle E' v vs"
  using inf_sup_ord(1,2)[of E E'] subgraph_cycle[of "E\<inter>E'"] by fast+

lemma cycle_from_node_inter:
  "cycle_from_node (E \<inter> E') v vs \<Longrightarrow> cycle_from_node E v vs"
  "cycle_from_node (E \<inter> E') v vs \<Longrightarrow> cycle_from_node E' v vs"
  using inf_sup_ord(1,2)[of E E'] subgraph_cycle_from_node[of "E\<inter>E'"] by fast+

(** If a lasso exists in the intersection of two graphs, it exists in both of those graphs *)
lemma lasso_from_node_inter:
  "lasso_from_node (E \<inter> E') x xs ys \<Longrightarrow> lasso_from_node E x xs ys"
  "lasso_from_node (E \<inter> E') x xs ys \<Longrightarrow> lasso_from_node E' x xs ys"
  using inf_sup_ord(1,2)[of E E'] subgraph_lasso[of "E\<inter>E'"] by fast+

lemma lasso_from_node'_inter:
  "lasso_from_node' (E \<inter> E') v vs \<Longrightarrow> lasso_from_node' E v vs"
  "lasso_from_node' (E \<inter> E') v vs \<Longrightarrow> lasso_from_node' E' v vs"
  using inf_sup_ord(1,2)[of E E'] subgraph_lasso'[of "E\<inter>E'"] by fast+
end