#include <deque>
#include "instance.h"
#include "solver.h"
#include "statistics.h"

class InteractiveSolver: Instance {
public:
    std::string last_result;

public:
    InteractiveSolver();

    void add_clause(int32_t const *clause, uint32_t size);

    void solve();

    bool simplePreProcess();

    bool prepFailedLiteralTest();

    void HardWireAndCompact();

    SOLVER_StateT countSAT();

    void decideLiteral();

    bool bcp();

    bool implicitBCP();

    bool BCP(unsigned start_at_stack_ofs);

    retStateT backtrack();

    retStateT resolveConflict();

    void recordLastUIPCauses();

    void recordAllUIPCauses();

    void minimizeAndStoreUIPClause(LiteralID uipLit, vector<LiteralID> &tmp_clause, bool seen[]);

    float scoreOf(VariableIndex v) {
        float score = comp_manager_.scoreOf(v);
        score += 10.0 * literal(LiteralID(v, true)).activity_score_;
        score += 10.0 * literal(LiteralID(v, false)).activity_score_;
        return score;
    }

    bool setLiteralIfFree(LiteralID lit, Antecedent ant = Antecedent(NOT_A_CLAUSE)) {
        if (literal_values_[lit] != X_TRI)
            return false;
        var(lit).decision_level = stack_.get_decision_level();
        var(lit).ante = ant;
        literal_stack_.push_back(lit);
        if (ant.isAClause() && ant.asCl() != NOT_A_CLAUSE)
            getHeaderOf(ant.asCl()).increaseScore();
        literal_values_[lit] = T_TRI;
        literal_values_[lit.neg()] = F_TRI;
        return true;
    }

    void setConflictState(LiteralID litA, LiteralID litB) {
        violated_clause.clear();
        violated_clause.push_back(litA);
        violated_clause.push_back(litB);
    }

    void setConflictState(ClauseOfs cl_ofs) {
        getHeaderOf(cl_ofs).increaseScore();
        violated_clause.clear();
        for (auto it = beginOf(cl_ofs); *it != SENTINEL_LIT; it++)
            violated_clause.push_back(*it);
    }

    vector<LiteralID>::const_iterator TOSLiteralsBegin() {
        return literal_stack_.begin() + stack_.top().literal_stack_ofs();
    }

    void initStack(unsigned int resSize) {
        stack_.clear();
        stack_.reserve(resSize);
        literal_stack_.clear();
        literal_stack_.reserve(resSize);
        stack_.push_back(StackLevel(1, 0, 2));
        stack_.back().changeBranch();
    }

    const LiteralID &TOS_decLit() {
        assert(stack_.top().literal_stack_ofs() < literal_stack_.size());
        return literal_stack_[stack_.top().literal_stack_ofs()];
    }

    void reactivateTOS() {
        for (auto it = TOSLiteralsBegin(); it != literal_stack_.end(); it++)
            unSet(*it);
        comp_manager_.cleanRemainingComponentsOf(stack_.top());
        literal_stack_.resize(stack_.top().literal_stack_ofs());
        stack_.top().resetRemainingComps();
    }

    int getAssertionLevel() const {
        return assertion_level_;
    }

private:
    SolverConfiguration config_;
    DecisionStack stack_;
    vector<LiteralID> literal_stack_;
    StopWatch stopwatch_;
    ComponentManager comp_manager_{config_, statistics_, literal_values_, &archetype_state};
    unsigned long last_ccl_deletion_time_{0};
    unsigned long last_ccl_cleanup_time_{0};
    vector<LiteralID> violated_clause;
    vector<vector<LiteralID> > uip_clauses_;
    int assertion_level_{0};
    unsigned int clauses_added{0};
    unsigned nVars{0};
    vector<LiteralID> implicitBCP_test_lits;
    LiteralIndexedVector<unsigned char> implicitBCP_viewed_lits;
    deque<LiteralID> minimizeAndStoreUIPClause_clause;
    vector<LiteralID> recordLastUIPCauses_tmp_clause;
    vector<LiteralID> recordAllUIPCauses_tmp_clause;
};
