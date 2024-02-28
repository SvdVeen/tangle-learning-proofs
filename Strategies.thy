theory Strategies
  imports Main Digraphs
begin

chapter \<open>Arenas and Strategies\<close>

section \<open>Arenas\<close>
(** An arena is a finite directed graph without dead ends, along with sets of vertices that belong
    to either player. We can get by with only specifying the even player's nodes, and getting the
    odd player's nodes by subtracting the even player's nodes from the set of all nodes *)
locale arena = finite_graph_V_succ +
  fixes V\<^sub>0 :: "'v set"
  assumes V\<^sub>0_in_V: "V\<^sub>0 \<subseteq> V"
begin

(** The odd player's nodes are all nodes in V that are not in V\<^sub>1 *)
abbreviation (input) V\<^sub>1 where "V\<^sub>1 \<equiv> V - V\<^sub>0"

(** V\<^sub>0 is the opposite of V\<^sub>1 because it is V\<^sub>1 subtracted from V *)
lemma V\<^sub>0_opposite_V\<^sub>1: "V\<^sub>0 = V - V\<^sub>1"
  using V\<^sub>0_in_V by blast

(** If a node is in V\<^sub>0, it is not in V\<^sub>1 and vice versa *)
lemma in_V\<^sub>1_notin_V\<^sub>0: "v\<in>V \<Longrightarrow> v\<notin>V\<^sub>0 \<longleftrightarrow> v\<in>V\<^sub>1" by blast
end (** End of locale arena *)

section \<open>Strategies\<close>
(** A positional strategy for a player \<alpha> is a function \<sigma>:V\<^sub>\<alpha>\<rightarrow>V *)
type_synonym 'v strat = "('v,'v) map"


subsection \<open>Edges of a Strategy\<close>
(** The set of edges in a strategy *)
definition E_of_strat :: "'v strat \<Rightarrow> 'v dgraph" where
  "E_of_strat \<sigma> = {(u,v). \<sigma> u = Some v}"

lemma E_of_strat_empty[simp]: "E_of_strat Map.empty = {}"
  unfolding E_of_strat_def by fast

(** If a strategy is part of another, its edges are a subset of the other strategy's edges *)
lemma strat_le_E_of_strat: "\<sigma> \<subseteq>\<^sub>m \<sigma>' \<Longrightarrow> E_of_strat \<sigma> \<subseteq> E_of_strat \<sigma>'"
  unfolding map_le_def E_of_strat_def by force

(** If the strategy leads to a w for some v, then (v,w) is an edge in the strategy *)
lemma edge_in_E_of_strat: "\<sigma> v = Some w \<longleftrightarrow> (v,w) \<in> E_of_strat \<sigma>"
  unfolding E_of_strat_def by simp

(** The domain of a strategy is equal to all source nodes in its edges *)
lemma E_of_strat_dom: "dom \<sigma> = fst`E_of_strat \<sigma>"
  unfolding E_of_strat_def by force

(** The range of a strategy is equal to all target nodes in its edges *)
lemma E_of_strat_ran: "ran \<sigma> = snd`E_of_strat \<sigma>"
  unfolding E_of_strat_def ran_def by force

context arena begin
subsection \<open>Strategies of Sets\<close>
(** Checks whether a strategy is in the graph and belongs to a particular player *)
definition strategy_of :: "'v set \<Rightarrow> 'v strat \<Rightarrow> bool" where
  "strategy_of S \<sigma> \<equiv> dom \<sigma> \<subseteq> S \<and> E_of_strat \<sigma> \<subseteq> E"

lemma strategy_of_empty[simp]: "strategy_of S Map.empty"
  unfolding strategy_of_def by auto

lemma strategy_of_empty_iff_empty_strategy[simp]: "strategy_of {} \<sigma> \<longleftrightarrow> \<sigma> = Map.empty"
  unfolding strategy_of_def by auto

(** If \<sigma> is a strategy of S, its domain is a subset of S *)
lemma strategy_of_dom: "strategy_of S \<sigma> \<Longrightarrow> dom \<sigma> \<subseteq> S"
  unfolding strategy_of_def by simp

(** If \<sigma> is a strategy of S, all of its edges are in the graph *)
lemma strategy_of_in_E: "strategy_of S \<sigma> \<Longrightarrow> E_of_strat \<sigma> \<subseteq> E"
  unfolding strategy_of_def by simp

(** A single mapping is a strategy of S if what it maps exists and the source is in S *)
lemma strategy_of_map_assign: "\<lbrakk>x\<in>S; (x,y)\<in>E\<rbrakk> \<Longrightarrow> strategy_of S [x\<mapsto>y]"
  unfolding strategy_of_def E_of_strat_def
  by (auto split: if_splits)

(** Adding two strategies of some S creates a strategy of that S *)
lemma strategy_of_add_same[simp]: "\<lbrakk>strategy_of S \<sigma>; strategy_of S \<sigma>'\<rbrakk> \<Longrightarrow> strategy_of S (\<sigma> ++ \<sigma>')"
  unfolding strategy_of_def E_of_strat_def by auto

(** If all edges of a strategy exist in E, it is also a strategy of its own domain *)
lemma strategy_of_own_dom: "E_of_strat \<sigma> \<subseteq> E \<Longrightarrow>  strategy_of (dom \<sigma>) \<sigma>"
  unfolding strategy_of_def by blast

(** If we overwrite a valid strategy with a valid move, the new strategy is also valid. *)
lemma strategy_of_overwrite: "\<lbrakk>strategy_of S \<sigma>; (x,y)\<in>E; x\<in>S\<rbrakk> \<Longrightarrow> strategy_of S (\<sigma>(x\<mapsto>y))"
  using strategy_of_map_assign[of x S y] strategy_of_add_same[of S \<sigma> "[x\<mapsto>y]"]
  by force

(** If we restrict a valid strategy, the new strategy remains valid. *)
lemma strategy_of_restrict: "strategy_of S \<sigma> \<Longrightarrow> strategy_of S (\<sigma> |` R)"
  unfolding strategy_of_def E_of_strat_def
  by (auto simp add: restrict_map_def split: if_splits)

subsection \<open>Induced Subgraphs\<close>
(** The induced subgraph of a strategy *)
definition induced_subgraph :: "'v strat \<Rightarrow> 'v dgraph" where
  "induced_subgraph \<sigma> = E \<inter> (((-dom \<sigma>) \<times> UNIV) \<union> E_of_strat \<sigma>)"

lemma ind_subgraph_empty[simp]: "induced_subgraph Map.empty = E"
  unfolding induced_subgraph_def using E_in_V by blast

(** The induced subgraph is a subgraph of the whole graph *)
lemma ind_subgraph[simp]: "induced_subgraph \<sigma> \<subseteq> E"
  unfolding induced_subgraph_def by auto
lemma ind_subgraph_edge_in_E[simp]: "(v,w) \<in> induced_subgraph \<sigma> \<Longrightarrow> (v,w) \<in> E"
  using ind_subgraph by blast

(** Induced subgraphs are finite *)
lemma ind_subgraph_finite[simp]: "finite (induced_subgraph \<sigma>)"
  using ind_subgraph fin_E finite_subset by blast

(** If an edge exists in the graph and its source is not in the domain of \<sigma>, it exists in the
    induced subgraph of \<sigma> *)
lemma ind_subgraph_notin_dom: "\<lbrakk>(v,w) \<in> E; v \<notin> dom \<sigma>\<rbrakk> \<Longrightarrow> (v,w) \<in> induced_subgraph \<sigma>"
  unfolding induced_subgraph_def by auto

(** If an edge exists in the induced subgraph of \<sigma> and it is in the domain, its destination is
    in the range of \<sigma> *)
lemma ind_subgraph_edge_dst: "\<lbrakk>(v,w) \<in> induced_subgraph \<sigma>; v \<in> dom \<sigma>\<rbrakk> \<Longrightarrow> w \<in> ran \<sigma>"
  unfolding induced_subgraph_def E_of_strat_def ran_def by blast

(** An induced subgraph in a closed region with a range into that region is closed in that
    region *)
lemma ind_subgraph_closed_region:
  "\<lbrakk>R\<subseteq>V; E `` (R \<inter> (V-dom \<sigma>)) \<subseteq> R; ran \<sigma> \<subseteq> R\<rbrakk> \<Longrightarrow> induced_subgraph \<sigma> `` R \<subseteq> R"
  using ind_subgraph_edge_dst ind_subgraph_edge_in_E by blast

(** If an edge is in an induced subgraph and its source is in the domain, the strategy maps its
    source to its target *)
lemma ind_subgraph_to_strategy: "\<lbrakk>(v, w) \<in> induced_subgraph \<sigma>; v \<in> dom \<sigma>\<rbrakk> \<Longrightarrow> \<sigma> v = Some w"
  unfolding induced_subgraph_def E_of_strat_def by blast

(** If a strategy maps a node to another, and that edge exists in the graph, it also exists in
    the induced subgraph *)
lemma strategy_to_ind_subgraph: "\<lbrakk>\<sigma> v = Some w; (v,w) \<in> E \<rbrakk> \<Longrightarrow> (v,w) \<in> induced_subgraph \<sigma>"
  unfolding induced_subgraph_def E_of_strat_def by auto

(** If you add two disjoint strategies, their combined induced subgraph is a subset of either of
    their induced subgraphs *)
lemma ind_subgraph_add_disjoint:
  assumes "dom \<sigma> \<inter> dom \<sigma>' = {}"
  shows "induced_subgraph (\<sigma> ++ \<sigma>') \<subseteq> induced_subgraph \<sigma>"
    and "induced_subgraph (\<sigma> ++ \<sigma>') \<subseteq> induced_subgraph \<sigma>'"
  using assms unfolding induced_subgraph_def E_of_strat_def by auto

(** If you add two strategies, any edge that does not start in one of their domains exists in
    the induced subgraph of the other strategy *)
lemma ind_subgraph_add_notin_dom:
  "\<lbrakk>(v,v')\<in>induced_subgraph (\<sigma> ++ \<sigma>'); v \<notin> dom \<sigma>'\<rbrakk>
    \<Longrightarrow> (v,v') \<in> induced_subgraph \<sigma>"
  "\<lbrakk>(v,v')\<in>induced_subgraph (\<sigma> ++ \<sigma>'); v \<notin> dom \<sigma>\<rbrakk>
    \<Longrightarrow> (v,v') \<in> induced_subgraph \<sigma>'"
  unfolding induced_subgraph_def E_of_strat_def
  using map_add_dom_app_simps by auto

(** Paths that exist in an induced subgraph also exist in the whole graph. Shorthand for an
    existing combination of lemmas *)
lemma ind_subgraph_path: "path (induced_subgraph \<sigma>) v xs v' \<Longrightarrow> path E v xs v'"
  using subgraph_path[OF ind_subgraph] .

(** Cycles that exist in an induced subgraph also exist in the whole graph. Shorthand for an
    existing combination of lemmas *)
lemma ind_subgraph_cycle: "cycle (induced_subgraph \<sigma>) v xs \<Longrightarrow> cycle E v xs"
  using subgraph_cycle[OF ind_subgraph] .

lemma ind_subgraph_reachable_cycle: "reachable_cycle (induced_subgraph \<sigma>) v xs
   \<Longrightarrow> reachable_cycle E v xs"
  using subgraph_reachable_cycle[OF ind_subgraph] .

(** Lassos that exist in and induced subgraph also exist in the whole graph. Shorthand for an
    existing combination of lemmas *)
lemma ind_subgraph_lasso: "lasso (induced_subgraph \<sigma>) x xs ys
  \<Longrightarrow> lasso E x xs ys"
  using subgraph_lasso[OF ind_subgraph] .

lemma ind_subgraph_lasso': "lasso' (induced_subgraph \<sigma>) v xs
  \<Longrightarrow> lasso' E v xs"
  using subgraph_lasso'[OF ind_subgraph] .


subsection \<open>Nodes in an Induced Subgraph\<close>
(** The set of all nodes in an induced subgraph *)
definition induced_subgraph_V :: "'v strat \<Rightarrow> 'v set" where
  "induced_subgraph_V \<sigma> \<equiv> EV (induced_subgraph \<sigma>)"

(** The nodes in an induced subgraph are a subset of V *)
lemma ind_subgraph_V_in_V[simp]: "induced_subgraph_V \<sigma> \<subseteq> V"
  unfolding induced_subgraph_V_def
  using ind_subgraph E_in_V by fastforce

(** The set of nodes in an induced subgraph is finite *)
lemma ind_subgraph_V_finite[simp]: "finite (induced_subgraph_V \<sigma>)"
  using finite_subset[OF ind_subgraph_V_in_V fin_V] by simp

(** An induced subgraph has nodes so long as it is valid and V is not empty. *)
lemma ind_subgraph_V_notempty:
  "\<lbrakk>V \<noteq> {}; E_of_strat \<sigma> \<subseteq> E\<rbrakk> \<Longrightarrow> induced_subgraph_V \<sigma> \<noteq> {}"
proof -
  assume "V \<noteq> {}" "E_of_strat \<sigma> \<subseteq> E"
  hence "E \<noteq> {}" using E_in_V succ by blast
  with \<open>E_of_strat \<sigma>\<subseteq>E\<close> show "induced_subgraph_V \<sigma> \<noteq> {}"
    unfolding induced_subgraph_V_def induced_subgraph_def E_of_strat_def
    apply (cases "dom \<sigma> = {}") by (auto simp: dom_def)
qed

subsection \<open>Induced Subgraphs in Subarenas\<close>
(** All nodes in an induced subgraph still have a successor *)
lemma ind_subgraph_succ: "\<lbrakk>v \<in> induced_subgraph_V \<sigma>; E_of_strat \<sigma> \<subseteq> E\<rbrakk>
  \<Longrightarrow> induced_subgraph \<sigma> `` {v} \<noteq> {}"
  apply (cases "v \<in> dom \<sigma>")
    subgoal using edge_in_E_of_strat[of \<sigma>] strategy_to_ind_subgraph by blast
    subgoal using ind_subgraph_notin_dom[of v] succ ind_subgraph_V_in_V by blast
    done

(** An induced subgraph is still a valid finite graph *)
lemma ind_subgraph_is_finite_graph[simp]:
  "finite_graph_V (induced_subgraph \<sigma>) (induced_subgraph_V \<sigma>)"
  apply (unfold_locales)
    subgoal unfolding induced_subgraph_V_def by force
    subgoal by simp
  done

(** An induced subgraph is still a valid finite graph without dead ends *)
lemma ind_subgraph_is_finite_graph_succ: "E_of_strat \<sigma> \<subseteq> E
  \<Longrightarrow> finite_graph_V_succ (induced_subgraph \<sigma>) (induced_subgraph_V \<sigma>)"
  apply (unfold_locales)
    subgoal unfolding induced_subgraph_V_def by force
    subgoal by simp
    subgoal using ind_subgraph_succ by simp
  done

(** Restricting an induced subgraph to the edges of a subarena means it is a subset of the same
    induced subgraph in that subarena *)
lemma ind_subgraph_restr_subarena:
  assumes "arena E' V' V\<^sub>0'"
  shows "induced_subgraph \<sigma> \<inter> E' \<subseteq> arena.induced_subgraph E' \<sigma>"
  unfolding induced_subgraph_def arena.induced_subgraph_def[OF assms] E_of_strat_def
  by blast


subsubsection \<open>Restricted Subgraphs\<close>
lemma restr_ind_subgraph:
  assumes "arena (Restr E R) (V\<inter>R) (V\<^sub>0\<inter>R)"
  shows "arena.induced_subgraph (Restr E R) \<sigma> = Restr (induced_subgraph \<sigma>) R"
  unfolding arena.induced_subgraph_def[OF assms] induced_subgraph_def
  by auto

subsubsection \<open>Restricted Strategies\<close>
lemma restricted_strat_subgraph_same_in_region:
  assumes "\<sigma>' = \<sigma> |` R"
  shows "Restr (induced_subgraph \<sigma>) R = Restr (induced_subgraph \<sigma>') R"
  unfolding assms induced_subgraph_def E_of_strat_def by auto

lemma restricted_strat_and_dom_subgraph_same_in_region:
  assumes "\<sigma>' = \<sigma> |` R"
  shows "Restr (induced_subgraph \<sigma>') R = Restr (induced_subgraph \<sigma>) R"
  unfolding assms(1) induced_subgraph_def E_of_strat_def by auto

lemma restricted_strat_subgraph_V_same_in_region:
  assumes "\<sigma>' = \<sigma> |` R"
  assumes "R \<subseteq> induced_subgraph_V  \<sigma>"
  shows "induced_subgraph_V \<sigma> \<inter> R = induced_subgraph_V \<sigma>' \<inter> R"
  using assms
  unfolding induced_subgraph_V_def induced_subgraph_def E_of_strat_def
  by auto
end (** End of locale arena *)

end
