theory ParityGames
imports Main Strategies
begin
(**
  Authors:
    - Suzanne van der Veen
    - Peter Lammich
    - Tom van Dijk

  This theory contains definitions for parity games and players.
*)
chapter \<open>Parity Games\<close>
section \<open>A General Parity Game\<close>
(** We define a parity game as an arena with a priority function. *)
locale paritygame = arena E V V\<^sub>0
  for E :: "'v dgraph" and V V\<^sub>0 :: "'v set" +
  fixes pr :: "'v \<Rightarrow> nat"
begin

(** Gives the top priority in a set of nodes. *)
definition pr_set :: "'v set \<Rightarrow> nat" where
  "pr_set S \<equiv> Max (pr ` S)"

(** Gives the top priority in a list. Used to determine which player wins a cycle. *)
definition pr_list :: "'v list \<Rightarrow> nat" where
  "pr_list xs \<equiv> pr_set (set xs)"

lemma pr_le_pr_set: "\<lbrakk>finite S; v \<in> S\<rbrakk> \<Longrightarrow> pr v \<le> pr_set S"
  unfolding pr_set_def by simp

(** The priority of any node in V is less than or equal to the top priority in V. *)
lemma pr_le_pr_set_V: "v \<in> V \<Longrightarrow> pr v \<le> pr_set V"
  using pr_le_pr_set by simp

(** In a nonempty finite set S, there always exists a v in S with its highest priority. *)
lemma pr_set_exists: "\<lbrakk>finite S; S\<noteq>{}\<rbrakk> \<Longrightarrow> \<exists>v\<in>S. pr v = pr_set S"
  unfolding pr_set_def
  using Max_in[of "pr ` S"] by fastforce

lemma pr_V_exists: "V \<noteq> {} \<Longrightarrow> \<exists>v\<in>V. pr v = pr_set V"
  using pr_set_exists by simp

(** The top priority in a nonempty region in V is less than or equal to the top priority
    in V. *)
lemma pr_set_le_pr_set_V:
  "\<lbrakk>S \<subseteq> V; S \<noteq> {}\<rbrakk> \<Longrightarrow> pr_set S \<le> pr_set V"
  unfolding pr_set_def
  using Max_mono[OF image_mono _ finite_imageI[OF fin_V]]
  by blast

(** The top priority in a nonempty list that is a subset of V is less than or equal to the top
    priority in V. *)
lemma pr_list_le_pr_set_V:
  "\<lbrakk>set xs \<subseteq> V; xs \<noteq> []\<rbrakk> \<Longrightarrow> pr_list xs \<le> pr_set V"
  unfolding pr_list_def
  using pr_set_le_pr_set_V
  by simp

(** If we have a node of the top priority in V in a list xs that is entirely in V, then the top
    priority in the list is equal to the top priority in V. *)
lemma pr_V_in_list:
  "\<lbrakk>set xs \<subseteq> V; v \<in> set xs; pr v = pr_set V\<rbrakk> \<Longrightarrow> pr_list xs = pr_set V"
  using pr_list_le_pr_set_V pr_le_pr_set[of "set xs"]
  unfolding pr_list_def by force

(** A valid subgame is a region in V that is a valid parity game. *)
abbreviation (input) valid_subgame :: "'v set \<Rightarrow> bool" where
  "valid_subgame R \<equiv> R \<subseteq> V \<and> paritygame (Restr E R) (V\<inter>R) (V\<^sub>0\<inter>R)"
end


section \<open>A Parity Game Bound to an Arbitrary Player\<close>
(** We define a parity game bound to an arbitrary player so we can prove properties for any non-
    specified player. *)
locale player_paritygame = paritygame E V V\<^sub>0 pr
  for E :: "'v dgraph" and V V\<^sub>0 :: "'v set" and pr :: "'v \<Rightarrow> nat" +
  fixes V\<^sub>\<alpha> :: "'v set"
  fixes winningP :: "nat \<Rightarrow> bool"
  assumes V\<^sub>\<alpha>_in_V: "V\<^sub>\<alpha> \<subseteq> V"
begin
(** Shorthand for the opponent's vertices. *)
abbreviation (input) V\<^sub>\<beta> :: "'v set" where
  "V\<^sub>\<beta> \<equiv> V-V\<^sub>\<alpha>"

(** V\<^sub>\<alpha> is the opposite of V\<^sub>\<beta> becuase it is V with V\<^sub>\<beta>. *)
lemma V\<^sub>\<alpha>_opposite_V\<^sub>\<beta>: "V\<^sub>\<alpha> = V-V\<^sub>\<beta>"
  using V\<^sub>\<alpha>_in_V by blast

(** If the player owns a node, it has successors in any strategy of the player's nodes,
    and its successors in any strategy of the opponent's nodes are the same as its successors
    in the entire graph. *)
lemma player_induced_succs:
  "\<lbrakk>v\<in>V\<^sub>\<alpha>; strategy_of V\<^sub>\<alpha> \<sigma>\<rbrakk> \<Longrightarrow> induced_subgraph \<sigma> `` {v} \<noteq> {}"
  "\<lbrakk>v\<in>V\<^sub>\<alpha>; strategy_of V\<^sub>\<beta> \<sigma>\<rbrakk> \<Longrightarrow> induced_subgraph \<sigma> `` {v} = E `` {v}"
  unfolding induced_subgraph_def E_of_strat_def strategy_of_def
  subgoal using succ[of v] V\<^sub>\<alpha>_in_V by (cases "v\<in>dom \<sigma>") blast+
  subgoal by auto
  done

(** If the opponent owns a node, it has successors in any strategy of the opponent's nondes,
    and its successors in any strategy of the player's nodes are the same as its successors
    in the entire graph. *)
lemma opponent_induced_succs:
  "\<lbrakk>v\<in>V\<^sub>\<beta>; strategy_of V\<^sub>\<beta> \<sigma>\<rbrakk> \<Longrightarrow> induced_subgraph \<sigma> `` {v} \<noteq> {}"
  "\<lbrakk>v\<in>V\<^sub>\<beta>; strategy_of V\<^sub>\<alpha> \<sigma>\<rbrakk> \<Longrightarrow> induced_subgraph \<sigma> `` {v} = E `` {v}"
  unfolding induced_subgraph_def E_of_strat_def strategy_of_def
  subgoal using succ[of v] by (cases "v\<in>dom \<sigma>") auto
  subgoal by auto
  done

lemma player_closed_ind_subgraph_opp:
  "\<lbrakk>induced_subgraph \<sigma> `` R \<subseteq> R'; strategy_of V\<^sub>\<alpha> \<sigma>\<rbrakk> \<Longrightarrow> E `` (V\<^sub>\<beta> \<inter> R) \<subseteq> R'"
  unfolding induced_subgraph_def E_of_strat_def strategy_of_def
  by auto

(** The intersection of two opposing players' induced subgraphs is a valid parity game. *)
lemma ind_subgraph_inter_opposed:
  assumes G\<sigma>: "G\<sigma> = induced_subgraph \<sigma>"
  assumes G\<sigma>': "G\<sigma>' = induced_subgraph \<sigma>'"
  assumes \<sigma>_player: "strategy_of V\<^sub>\<alpha> \<sigma>"
  assumes \<sigma>'_opp: "strategy_of V\<^sub>\<beta> \<sigma>'"
  shows "paritygame (G\<sigma> \<inter> G\<sigma>') V V\<^sub>0"
  using assms V\<^sub>0_in_V E_in_V
  apply (unfold_locales; clarsimp)
  subgoal using ind_subgraph by blast
  subgoal for v apply (cases "v\<in>V\<^sub>\<alpha>")
    subgoal using player_induced_succs[of v] by fastforce
    subgoal using opponent_induced_succs[of v] by fastforce
    done
  done
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
  by auto

abbreviation player_wins_list :: "player \<Rightarrow> 'v list \<Rightarrow> bool" where
  "player_wins_list \<alpha> xs \<equiv> player_winningP \<alpha> (pr_list xs)"

(** Gives the vertices belonging to a player. *)
fun V_player where
  "V_player EVEN = V\<^sub>0"
| "V_player ODD = V\<^sub>1"

lemma V_player_in_V: "V_player \<alpha> \<subseteq> V"
  using V\<^sub>0_in_V by (cases \<alpha>; simp)

(** Gives the vertices belonging to a player's opponent. *)
fun V_opponent where
  "V_opponent EVEN = V\<^sub>1"
| "V_opponent ODD = V\<^sub>0"

lemma V_opponent_in_V: "V_opponent \<alpha> \<subseteq> V"
  using V\<^sub>0_in_V by (cases \<alpha>; simp)

lemma V_player_opponent: "V_player (opponent \<alpha>) = V_opponent \<alpha>"
  by (cases \<alpha>) auto

lemma V_opponent_opponent: "V_opponent (opponent \<alpha>) = V_player \<alpha>"
  by (cases \<alpha>) auto

lemma V_player_opposite_V_opponent: "V_player \<alpha> = V - V_opponent \<alpha>"
  using V\<^sub>0_in_V by (cases \<alpha>; simp) blast

lemma V_opponent_opposite_V_player: "V_opponent \<alpha> = V - V_player \<alpha>"
  using V\<^sub>0_in_V by (cases \<alpha>; simp) blast

lemma v_notin_V_player_in_V_opponent: "v\<in>V \<Longrightarrow> v \<notin> V_player \<alpha> \<longleftrightarrow> v \<in> V_opponent \<alpha>"
  using V_player_opposite_V_opponent by auto

lemma restr_subgraph_V_player:
  assumes "paritygame (Restr E R) (V\<inter>R) (V\<^sub>0\<inter>R)"
  shows "paritygame.V_player (V\<inter>R) (V\<^sub>0\<inter>R) \<alpha> = V_player \<alpha> \<inter> R"
  using paritygame.V_player.simps[OF assms]
  by (cases \<alpha>; simp) blast

lemma restr_subgraph_V_opponent:
  assumes "paritygame (Restr E R) (V\<inter>R) (V\<^sub>0\<inter>R)"
  shows "paritygame.V_opponent (V\<inter>R) (V\<^sub>0\<inter>R) \<alpha> = V_opponent \<alpha> \<inter> R"
  using paritygame.V_opponent.simps[OF assms]
  by (cases \<alpha>; simp) blast

(** Checks that a strategy belongs to a specific player. *)
definition strategy_of_player :: "player \<Rightarrow> 'v strat \<Rightarrow> bool" where
  "strategy_of_player \<alpha> \<sigma> \<equiv> strategy_of (V_player \<alpha>) \<sigma>"

lemma player_strat_dom: "strategy_of_player \<alpha> \<sigma> \<Longrightarrow> dom \<sigma> \<subseteq> V_player \<alpha>"
  unfolding strategy_of_player_def strategy_of_def by simp

lemma player_strat_in_E: "strategy_of_player \<alpha> \<sigma> \<Longrightarrow> E_of_strat \<sigma> \<subseteq> E"
  unfolding strategy_of_player_def strategy_of_def by simp

lemma closed_ind_subgraph_opp:
  "\<lbrakk>induced_subgraph \<sigma> `` R \<subseteq> R'; strategy_of_player \<alpha> \<sigma>\<rbrakk>
    \<Longrightarrow> E `` (V_opponent \<alpha> \<inter> R) \<subseteq> R'"
  unfolding strategy_of_player_def
  using P0.player_closed_ind_subgraph_opp
  using P1.player_closed_ind_subgraph_opp
  apply (cases \<alpha>; simp)
  using V_opponent.simps(2) V_opponent_opposite_V_player by auto

lemma restr_subgraph_strat_of_player:
  assumes "paritygame (Restr E R) (V\<inter>R) (V\<^sub>0\<inter>R)"
  shows "paritygame.strategy_of_player (Restr E R) (V\<inter>R) (V\<^sub>0\<inter>R) \<alpha> \<sigma>
    \<Longrightarrow> strategy_of (V_player \<alpha>) \<sigma>"
  unfolding paritygame.strategy_of_player_def[OF assms]
  unfolding restr_subgraph_V_player[OF assms]
  unfolding arena.strategy_of_def[OF paritygame.axioms[OF assms]]
  unfolding strategy_of_def
  by simp
end (** End of context paritygame. *)

end
