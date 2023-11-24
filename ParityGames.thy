theory ParityGames
imports Main Strategies
begin
chapter \<open>Parity Games\<close>
section \<open>A General Parity Game\<close>
(** We define a parity game as an arena with a priority function. *)
locale paritygame = arena E V V\<^sub>0
  for E V and V\<^sub>0 :: "'v set" +
  fixes pr :: "'v \<Rightarrow> nat"
begin
  (** Gives the top priority in a list. Used to determine which player wins a cycle. *)
  definition top_pr :: "'v list \<Rightarrow> nat" where
    "top_pr xs \<equiv> MAX v \<in> set xs. pr v"

  (** Gives the top priority in a set of nodes. *)
  definition pr_set :: "'v set \<Rightarrow> nat" where
    "pr_set S \<equiv> Max (pr ` S)"

  lemma pr_le_pr_set: "\<lbrakk>finite S; v \<in> S\<rbrakk> \<Longrightarrow> pr v \<le> pr_set S"
    unfolding pr_set_def by simp

  (** The priority of any node in V is less than or equal to the top priority in V. *)
  lemma pr_le_pr_set_V: "v \<in> V \<Longrightarrow> pr v \<le> pr_set V"
    using pr_le_pr_set by simp

  (** In a nonempty finite set S, there always exists a v in S with its highest priority. *)
  lemma pr_set_exists: "\<lbrakk>finite S; S\<noteq>{}\<rbrakk> \<Longrightarrow> \<exists>v\<in>S. pr v = pr_set S"
    unfolding pr_set_def
    using Max_in[of "pr ` S"] by fastforce

  (** The top priority in a nonempty list that is a subset of V is less than or equal to the top
      priority in V. *)
  lemma top_pr_le_pr_set_V: "\<lbrakk>set xs \<subseteq> V; xs \<noteq> []\<rbrakk> \<Longrightarrow> top_pr xs \<le> pr_set V"
    unfolding top_pr_def pr_set_def
    using image_mono Max_mono by auto
end


section \<open>A Parity Game Bound to an Arbitrary Player\<close>
(** We define a parity game bound to an arbitrary player so we can prove properties for any non-
    specified player. *)
locale player_paritygame = paritygame E V V\<^sub>0 pr
  for E V and V\<^sub>0 :: "'v set" and pr +
  fixes V\<^sub>\<alpha> :: "'v set"
  fixes winningP :: "nat \<Rightarrow> bool"
  assumes V\<^sub>\<alpha>_subset: "V\<^sub>\<alpha> \<subseteq> V"
  assumes V\<^sub>\<alpha>_player: "V\<^sub>\<alpha> = V\<^sub>0 \<or> V\<^sub>\<alpha> = V\<^sub>1"
begin
(** Shorthand for the opponent's vertices. *)
abbreviation (input) V\<^sub>\<beta> :: "'v set" where
  "V\<^sub>\<beta> \<equiv> V-V\<^sub>\<alpha>"

(** If the player owns a node, it has successors in any strategy of the player's nodes,
    and its successors in any strategy of the opponent's nodes are the same as its successors
    in the entire graph. *)
lemma player_induced_succs:
  "\<lbrakk>v\<in>V\<^sub>\<alpha>; strategy_of V\<^sub>\<alpha> \<sigma>\<rbrakk> \<Longrightarrow> induced_subgraph (dom \<sigma>) \<sigma> `` {v} \<noteq> {}"
  "\<lbrakk>v\<in>V\<^sub>\<alpha>; strategy_of V\<^sub>\<beta> \<sigma>\<rbrakk> \<Longrightarrow> induced_subgraph (dom \<sigma>) \<sigma> `` {v} = E `` {v}"
  unfolding induced_subgraph_def E_of_strat_def strategy_of_def V\<^sub>1_def
    subgoal using succ[of v] V\<^sub>\<alpha>_subset apply (cases "v\<in>dom \<sigma>") by blast+
    subgoal by auto
  done

(** If the opponent owns a node, it has successors in any strategy of the opponent's nondes,
    and its successors in any strategy of the player's nodes are the same as its successors
    in the entire graph. *)
lemma opponent_induced_succs:
  "\<lbrakk>v\<in>V\<^sub>\<beta>; strategy_of V\<^sub>\<beta> \<sigma>\<rbrakk> \<Longrightarrow> induced_subgraph (dom \<sigma>) \<sigma> `` {v} \<noteq> {}"
  "\<lbrakk>v\<in>V\<^sub>\<beta>; strategy_of V\<^sub>\<alpha> \<sigma>\<rbrakk> \<Longrightarrow> induced_subgraph (dom \<sigma>) \<sigma> `` {v} = E `` {v}"
  unfolding induced_subgraph_def E_of_strat_def strategy_of_def V\<^sub>1_def
    subgoal using succ[of v] by (cases "v\<in>dom \<sigma>") auto
    subgoal by auto
  done

(** The intersection of two opposing players' induced subgraphs is a valid parity game. *)
lemma ind_subgraph_inter_opposed:
  assumes G\<sigma>: "G\<sigma> = induced_subgraph (dom \<sigma>) \<sigma>"
  assumes G\<sigma>': "G\<sigma>' = induced_subgraph (dom \<sigma>') \<sigma>'"
  assumes \<sigma>_player: "strategy_of V\<^sub>\<alpha> \<sigma>"
  assumes \<sigma>'_opp: "strategy_of V\<^sub>\<beta> \<sigma>'"
  shows "paritygame (G\<sigma> \<inter> G\<sigma>') V V\<^sub>0"
proof (unfold_locales)
  show "G\<sigma> \<inter> G\<sigma>' \<subseteq> V\<times>V"
    unfolding G\<sigma> using ind_subgraph E_in_V by blast
  show "finite V" by simp
  show "V\<^sub>0\<subseteq>V" using V\<^sub>0_in_V by simp
  show "\<And>v. v \<in> V \<Longrightarrow> (G\<sigma> \<inter> G\<sigma>') `` {v} \<noteq> {}"
  proof (cases)
    fix v
    assume v_player: "v\<in>V\<^sub>\<alpha>"
    with \<sigma>'_opp have "G\<sigma>' `` {v} = E `` {v}"
      unfolding G\<sigma>' using player_induced_succs by simp
    moreover from v_player \<sigma>_player have "G\<sigma> `` {v} \<noteq> {}"
      unfolding G\<sigma> using player_induced_succs by blast
    moreover have "G\<sigma> \<subseteq> E" unfolding G\<sigma> by simp
    ultimately show "(G\<sigma> \<inter> G\<sigma>') `` {v} \<noteq> {}" by auto
  next
    fix v
    assume "v\<in>V" "v\<notin>V\<^sub>\<alpha>"
    hence v_opp: "v\<in>V-V\<^sub>\<alpha>" by auto
    with \<sigma>_player have "G\<sigma> `` {v} = E `` {v}"
      unfolding G\<sigma> using opponent_induced_succs by simp
    moreover from v_opp \<sigma>'_opp have "G\<sigma>' `` {v} \<noteq> {}"
      unfolding G\<sigma>' using opponent_induced_succs by simp
    moreover have "G\<sigma>' \<subseteq> E" unfolding G\<sigma>' using ind_subgraph by simp
    ultimately show "(G\<sigma> \<inter> G\<sigma>') `` {v} \<noteq> {}" using succ[of v] by blast
  qed
qed
end (** End of locale player_paritygame. *)


(** Now that we have definitions for non-specific players, we need to introduce definitions for the
    actual players of parity games. *)
section \<open>Specific Players\<close>
(** There are two players: Even and Odd. *)
datatype player = EVEN | ODD

(** Gets the opponent of a given player. *)
fun opponent where
  "opponent EVEN = ODD"
| "opponent ODD = EVEN"

lemma opponent2[simp]: "opponent (opponent \<alpha>) = \<alpha>"
  by (cases \<alpha>) auto

(** Gives the player that would win a priority. *)
definition player_wins_pr :: "nat \<Rightarrow> player" where
  "player_wins_pr p \<equiv> if even p then EVEN else ODD"

(** Gives the winning priority function for the players. *)
fun player_winningP :: "player \<Rightarrow> nat \<Rightarrow> bool" where
  "player_winningP EVEN = even"
| "player_winningP ODD = odd"


subsection \<open>Specific Players in a Parity Game\<close>
context paritygame begin
(** We can see a parity game as two player-specific parity games for either player. *)
sublocale P0: player_paritygame E V V\<^sub>0 pr V\<^sub>0 even
  apply unfold_locales
  by (auto simp: V\<^sub>0_in_V)

sublocale P1: player_paritygame E V V\<^sub>0 pr V\<^sub>1 odd
  apply unfold_locales
  by (auto simp: V\<^sub>1_in_V)

abbreviation player_wins_list :: "player \<Rightarrow> 'v list \<Rightarrow> bool" where
  "player_wins_list \<alpha> xs \<equiv> player_winningP \<alpha> (top_pr xs)"

(** Gives the vertices belonging to a player. *)
fun V_player where
  "V_player EVEN = V\<^sub>0"
| "V_player ODD = V\<^sub>1"

(** Gives the vertices belonging to a player's opponent. *)
fun V_opponent where
  "V_opponent EVEN = V\<^sub>1"
| "V_opponent ODD = V\<^sub>0"

lemma V_player_opponent: "V_player (opponent \<alpha>) = V_opponent \<alpha>"
  by (cases \<alpha>) auto

lemma V_opponent_opponent: "V_opponent (opponent \<alpha>) = V_player \<alpha>"
  by (cases \<alpha>) auto

lemma V_diff_diff_V\<^sub>0: "(V - (V - V\<^sub>0)) = V\<^sub>0"
  by (simp add: V\<^sub>0_in_V double_diff)

lemma V_player_opposite_V_opponent: "V_player \<alpha> = V - V_opponent \<alpha>"
  using V_diff_diff_V\<^sub>0 by (cases \<alpha>; simp add: V\<^sub>1_def)

lemma V_opponent_opposite_V_player: "V_opponent \<alpha> = V - V_player \<alpha>"
    using V_diff_diff_V\<^sub>0 by (cases \<alpha>; simp add: V\<^sub>1_def)

lemma V_opponent_player_int: "V' \<subseteq> V \<Longrightarrow> V' \<inter> V_opponent \<alpha> = V' - V_player \<alpha>"
  using V\<^sub>1_def by (cases \<alpha>) auto

lemma v_notin_V_player_in_V_opponent: "v\<in>V \<Longrightarrow> v \<notin> V_player \<alpha> \<longleftrightarrow> v \<in> V_opponent \<alpha>"
  using V_player_opposite_V_opponent by auto

lemma restr_subgraph_V_player:
  assumes "paritygame (Restr E R) (V\<inter>R) (V\<^sub>0\<inter>R)"
  shows "paritygame.V_player (V\<inter>R) (V\<^sub>0\<inter>R) \<alpha> = V_player \<alpha> \<inter> R"
  using paritygame.V_player.simps[OF assms]
  apply (cases \<alpha>; simp add: arena.V\<^sub>1_def[OF paritygame.axioms[OF assms]] V\<^sub>1_def)
  by blast

lemma restr_subgraph_V_opponent:
  assumes "paritygame (Restr E R) (V\<inter>R) (V\<^sub>0\<inter>R)"
  shows "paritygame.V_opponent (V\<inter>R) (V\<^sub>0\<inter>R) \<alpha> = V_opponent \<alpha> \<inter> R"
  using paritygame.V_opponent.simps[OF assms]
  apply (cases \<alpha>; simp add: arena.V\<^sub>1_def[OF paritygame.axioms[OF assms]] V\<^sub>1_def)
  by blast

(** Checks that a strategy belongs to a specific player. *)
definition strategy_of_player :: "player \<Rightarrow> 'v strat \<Rightarrow> bool" where
  "strategy_of_player \<alpha> \<sigma> \<equiv> strategy_of (V_player \<alpha>) \<sigma>"

lemma player_strat_dom: "strategy_of_player \<alpha> \<sigma> \<Longrightarrow> dom \<sigma> \<subseteq> V_player \<alpha>"
  unfolding strategy_of_player_def strategy_of_def by simp

lemma player_strat_in_E: "strategy_of_player \<alpha> \<sigma> \<Longrightarrow> E_of_strat \<sigma> \<subseteq> E"
  unfolding strategy_of_player_def strategy_of_def by simp

lemma restr_subgraph_strategy_of_player:
  assumes "paritygame (Restr E R) (V\<inter>R) (V\<^sub>0\<inter>R)"
  shows "paritygame.strategy_of_player (Restr E R) (V \<inter> R) (V\<^sub>0 \<inter> R) \<alpha> \<sigma>
    \<Longrightarrow> strategy_of (V_player \<alpha>) \<sigma>"
  unfolding paritygame.strategy_of_player_def[OF assms]
  unfolding restr_subgraph_V_player[OF assms]
  unfolding arena.strategy_of_def[OF paritygame.axioms[OF assms]]
  unfolding strategy_of_def
  by simp
end (** End of context paritygame. *)

end
