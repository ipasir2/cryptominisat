/******************************************
 * 
 * IPASIR-2 by Markus Iser, 2023
 * 
 * Build upon IPASIR for CryptoMiniSat
 * 
Copyright (c) 2014, Tomas Balyo, Karlsruhe Institute of Technology.
Copyright (c) 2014, Armin Biere, Johannes Kepler University.

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to
deal in the Software without restriction, including without limitation the
rights to use, copy, modify, merge, publish, distribute, sublicense, and/or
sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS
IN THE SOFTWARE.
***********************************************/

#include "cryptominisat.h"
#include "solverconf.h"
#include "solver.h"
#include <vector>
#include <complex>
#include <cassert>
#include <string.h>
#include "constants.h"

class SolverWrapper {
    CMSat::Solver* solver;

    std::vector<CMSat::Lit> assumptions;
    std::vector<CMSat::Lit> clause;

    std::vector<uint8_t> is_failed_assumption;

    enum solver_state {
        STATE_INPUT,
        STATE_SAT,
        STATE_UNSAT,
    } state;

    void createVarIfNotExists(int32_t lit) {
        if (abs(lit) > solver->nVars()) {
            solver->new_vars(abs(lit) - solver->nVars());
        }
        if (abs(lit)*2 > is_failed_assumption.size()) {
            is_failed_assumption.resize(abs(lit)*2, 0);
        }
    }

    CMSat::Lit toCMSatLit(int32_t lit) {
        return CMSat::Lit(abs(lit)-1, lit < 0);
    }

public:
    SolverWrapper() : assumptions(), clause(), state(STATE_INPUT) {
        solver = new CMSat::Solver;
    }

    ~SolverWrapper() {
        delete solver;
    }

    bool configure(const char* name, int value) {
        CMSat::SolverConf conf = solver->getConf();
        if (strcmp(name, "branch_strategy_setup") == 0) {
            switch (value) {
                case 0: 
                    conf.branch_strategy_setup = "vsids";
                    break;
                case 1:
                    conf.branch_strategy_setup = "vmtf";
                    break;
                case 2:
                    conf.branch_strategy_setup = "rand";
                    break;
                case 3:
                    conf.branch_strategy_setup = "vmtf+vsids";
                    break;
            }
        }
        else if (strcmp(name, "restartType") == 0) {
            conf.restartType = CMSat::Restart(value);
        }
        else if (strcmp(name, "polarity_mode") == 0) {
            conf.polarity_mode = CMSat::PolarityMode(value);
        }
        else if (strcmp(name, "glue_put_lev0_if_below_or_eq") == 0) {
            conf.glue_put_lev0_if_below_or_eq = value;
        }
        else if (strcmp(name, "glue_put_lev1_if_below_or_eq") == 0) {
            conf.glue_put_lev1_if_below_or_eq = value;
        }
        else if (strcmp(name, "every_lev1_reduce") == 0) {
            conf.every_lev1_reduce = value;
        }
        else if (strcmp(name, "every_lev2_reduce") == 0) {
            conf.every_lev2_reduce = value;
        }
        else if (strcmp(name, "do_bva") == 0) {
            conf.do_bva = value;
        }
        else if (strcmp(name, "max_temp_lev2_learnt_clauses") == 0) {
            conf.max_temp_lev2_learnt_clauses = value;
        }
        else if (strcmp(name, "never_stop_search") == 0) {
            conf.never_stop_search = value;
        }
        else if (strcmp(name, "doMinimRedMoreMore") == 0) {
            conf.doMinimRedMoreMore = value;
        }
        else if (strcmp(name, "max_num_lits_more_more_red_min") == 0) {
            conf.max_num_lits_more_more_red_min = value;
        }
        else if (strcmp(name, "max_glue_more_minim") == 0) {
            conf.max_glue_more_minim = value;
        }
        else if (strcmp(name, "orig_global_timeout_multiplier") == 0) {
            conf.orig_global_timeout_multiplier = value;
        }
        else if (strcmp(name, "more_red_minim_limit_binary") == 0) {
            conf.more_red_minim_limit_binary = value;
        }
        else if (strcmp(name, "restart_first") == 0) {
            conf.restart_first = value;
        }
        solver->setConf(conf);
    }

    bool configure(const char* name, float value) {
        CMSat::SolverConf conf = solver->getConf();
        if (strcmp(name, "varElimRatioPerIter") == 0) {
            conf.varElimRatioPerIter = value;
        }
        else if (strcmp(name, "inc_max_temp_lev2_red_cls") == 0) {
            conf.inc_max_temp_lev2_red_cls = value;
        }
        else if (strcmp(name, "num_conflicts_of_search_inc") == 0) {
            conf.num_conflicts_of_search_inc = value;
        }
        else if (strcmp(name, "restart_inc") == 0) {
            conf.restart_inc = value;
        }
        solver->setConf(conf);
    }

    void add(int32_t lit) {
        if (state == STATE_UNSAT) {
            std::fill(is_failed_assumption.begin(), is_failed_assumption.end(), 0);
        }
        state = STATE_INPUT;
        createVarIfNotExists(lit);
        if (lit == 0) {
            solver->add_clause_outside(clause);
            clause.clear();
        } 
        else {
            clause.push_back(toCMSatLit(lit));
        }
    }

    void assume(int32_t lit) {
        if (state == STATE_UNSAT) {
            std::fill(is_failed_assumption.begin(), is_failed_assumption.end(), 0);
        }
        state = STATE_INPUT;
        createVarIfNotExists(lit);
        assumptions.push_back(toCMSatLit(lit));
    }

    int solve() {
        CMSat::lbool ret = solver->solve_with_assumptions(&assumptions);
        assumptions.clear();
        std::fill(is_failed_assumption.begin(), is_failed_assumption.end(), 0);

        if (ret == CMSat::l_True) {
            state = STATE_SAT;
            return 10;
        }
        else if (ret == CMSat::l_False) {
            for (CMSat::Lit failed : solver->get_final_conflict()) {
                is_failed_assumption[failed.toInt()] = 1;
            }
            state = STATE_UNSAT;
            return 20;
        }
        else if (ret == CMSat::l_Undef) {
            state = STATE_INPUT;
            return 0;
        }
        return -1;
    }

    int val(int32_t lit) {
        if (state != STATE_SAT) {
            return 0;
        }
        CMSat::lbool res = solver->get_model()[abs(lit)-1];
        if (res == CMSat::l_True) {
            return lit;
        }
        else if (res == CMSat::l_False) {
            return -lit;
        }
    }

    int failed(int32_t lit) {
        if (state != STATE_UNSAT) {
            return 0;
        }
        if (is_failed_assumption[toCMSatLit(-lit).toInt()]) {
            return lit;
        }
        return 0;
    }
};

extern "C" {
    #include "ipasir2.h"

    ipasir2_errorcode ipasir2_signature(const char** signature) {
        static char tmp[200];
        std::string tmp2 = "cryptominisat-";
        tmp2 += CMSat::SATSolver::get_version();
        memcpy(tmp, tmp2.c_str(), tmp2.length()+1);
        *signature = tmp;
        return IPASIR_E_OK;
    }

    ipasir2_errorcode ipasir2_init(void** solver) {
        *solver = (void*)new SolverWrapper();
        return IPASIR_E_OK;
    }

    ipasir2_errorcode ipasir2_release(void* solver) {
        delete (SolverWrapper*)solver;
        return IPASIR_E_OK;
    }

    ipasir2_errorcode ipasir2_options(void* solver, ipasir2_option const** options) {    
        ipasir2_option* solver_options = new ipasir2_option[21];
        solver_options[0] = { "branch_strategy_setup", ipasir2_option_type::INT, 0, 3 };
        solver_options[1] = { "varElimRatioPerIter", ipasir2_option_type::FLOAT, {._flt=0.1}, {._flt=1.0} };
        solver_options[2] = { "restartType", ipasir2_option_type::INT, 0, 4 };
        solver_options[3] = { "polarity_mode", ipasir2_option_type::INT, 0, 7 };
        solver_options[4] = { "inc_max_temp_lev2_red_cls", ipasir2_option_type::FLOAT, {._flt=1.0}, {._flt=.04} };
        solver_options[5] = { "glue_put_lev0_if_below_or_eq", ipasir2_option_type::INT, 0, 4 };
        solver_options[6] = { "glue_put_lev1_if_below_or_eq", ipasir2_option_type::INT, 0, 6 };
        solver_options[7] = { "every_lev1_reduce", ipasir2_option_type::INT, 1, 10000 };
        solver_options[8] = { "every_lev2_reduce", ipasir2_option_type::INT, 1, 15000 };
        solver_options[9] = { "do_bva", ipasir2_option_type::INT, 0, 1 };
        solver_options[10] = { "max_temp_lev2_learnt_clauses", ipasir2_option_type::INT, 10000, 30000 };
        solver_options[11] = { "never_stop_search", ipasir2_option_type::INT, 0, 1 };
        solver_options[12] = { "doMinimRedMoreMore", ipasir2_option_type::INT, 0, 2 };
        solver_options[13] = { "max_num_lits_more_more_red_min", ipasir2_option_type::INT, 0, 20 };
        solver_options[14] = { "max_glue_more_minim", ipasir2_option_type::INT, 0, 4 };
        solver_options[15] = { "orig_global_timeout_multiplier", ipasir2_option_type::INT, 0, 5 };
        solver_options[16] = { "num_conflicts_of_search_inc", ipasir2_option_type::FLOAT, {._flt=1.0}, {._flt=1.15} };
        solver_options[17] = { "more_red_minim_limit_binary", ipasir2_option_type::INT, 0, 600 };
        solver_options[18] = { "restart_inc", ipasir2_option_type::FLOAT, {._flt=1.1}, {._flt=1.5} };
        solver_options[19] = { "restart_first", ipasir2_option_type::INT, 100, 500 };
        solver_options[20] = { 0 };
        *options = solver_options;
        return IPASIR_E_OK;
    }

    ipasir2_errorcode ipasir2_set_option(void* solver, const char* name, ipasir2_option_value value) {
        const ipasir2_option* options;
        ipasir2_options(solver, &options);
        for (const ipasir2_option* opt = options; opt != 0; ++opt) {
            if (strcmp(opt->name, name) == 0) {
                if (opt->type == ipasir2_option_type::INT) {
                    if (value._int < opt->min._int || value._int > opt->max._int) {
                        return IPASIR_E_OPTION_INVALID_VALUE;
                    }
                    ((SolverWrapper*)solver)->configure(name, value._int);
                    return IPASIR_E_OK;
                }
                else if (opt->type == ipasir2_option_type::FLOAT) {
                    if (value._flt < opt->min._flt || value._flt > opt->max._flt) {
                        return IPASIR_E_OPTION_INVALID_VALUE;
                    }
                    ((SolverWrapper*)solver)->configure(name, value._flt);
                    return IPASIR_E_OK;
                }
                else {
                    return IPASIR_E_OPTION_INVALID_VALUE;
                }
            }
        }
        return IPASIR_E_OPTION_UNKNOWN;
    }

    ipasir2_errorcode ipasir2_add(void* solver, int lit_or_zero) {
        ((SolverWrapper*)solver)->add(lit_or_zero);
        return IPASIR_E_OK;
    }

    ipasir2_errorcode ipasir2_assume(void* solver, int lit) {
        ((SolverWrapper*)solver)->assume(lit);
        return IPASIR_E_OK;
    }

    ipasir2_errorcode ipasir2_solve(void* solver, int32_t* status) {
        *status = ((SolverWrapper*)solver)->solve();
        if (*status == -1) {
            return IPASIR_E_UNKNOWN;
        }
        return IPASIR_E_OK;
    }

    ipasir2_errorcode ipasir2_val(void* solver, int32_t lit, int32_t* val) {
        *val = ((SolverWrapper*)solver)->val(lit);
        return IPASIR_E_OK;
    }

    ipasir2_errorcode ipasir2_failed(void* solver, int32_t lit, int32_t* failed) {
        *failed = ((SolverWrapper*)solver)->failed(lit);
        return IPASIR_E_OK;
    }

    // TODO
    ipasir2_errorcode ipasir2_assignment_size(void* solver, int32_t* size) {
        return IPASIR_E_UNSUPPORTED;
    }

    // TODO
    ipasir2_errorcode ipasir2_assignment(void* solver, int32_t index, int32_t* lit) {
        return IPASIR_E_UNSUPPORTED;
    }

    ipasir2_errorcode ipasir2_set_terminate(void* solver, void* state, int (*terminate)(void* state)) {
        return IPASIR_E_UNSUPPORTED;
    }

    ipasir2_errorcode ipasir2_set_learn(void* solver, void* state, void (*learn)(void* state, int* clause)) {
        return IPASIR_E_UNSUPPORTED;
    }

    // TODO
    ipasir2_errorcode ipasir2_set_import_redundant_clause(void* solver, void* state, void (*import)(void* state, int32_t** clause)) {
        return IPASIR_E_UNSUPPORTED;
    }

}
