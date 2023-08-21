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

#include "ipasir2.h"
#include "cryptominisat.h"
#include "solverconf.h"
#include "solver.h"
#include <vector>
#include <complex>
#include <cassert>
#include <string.h>
#include "constants.h"

class SolverWrapper {
    CMSat::SolverConf* conf;
    std::atomic<bool> terminate;

    CMSat::Solver* solver;

    std::vector<CMSat::Lit> assumptions;
    std::vector<CMSat::Lit> clause;

    std::vector<uint8_t> is_failed_assumption;

    ipasir2_state state;

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
    SolverWrapper() : conf(), terminate(), assumptions(), clause(), state(IPASIR2_S_CONFIG) {
        conf = new CMSat::SolverConf();
        solver = nullptr;
    }

    ~SolverWrapper() {
        delete solver;
    }

    CMSat::SolverConf* getConf() {
        return conf;
    }

    ipasir2_state getState() {
        return state;
    }

    void add(int32_t lit) {
        if (state == IPASIR2_S_UNSAT) {
            std::fill(is_failed_assumption.begin(), is_failed_assumption.end(), 0);
        }
        else if (solver == nullptr) {
            solver = new CMSat::Solver(conf, &terminate);
        }
        state = IPASIR2_S_INPUT;
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
        if (state == IPASIR2_S_UNSAT) {
            std::fill(is_failed_assumption.begin(), is_failed_assumption.end(), 0);
        }
        else if (solver == nullptr) {
            solver = new CMSat::Solver(conf, &terminate);
        }
        state = IPASIR2_S_INPUT;
        createVarIfNotExists(lit);
        assumptions.push_back(toCMSatLit(lit));
    }

    int solve() {
        if (solver == nullptr) {
            solver = new CMSat::Solver(conf, &terminate);
            state = IPASIR2_S_SOLVING;
        }
        CMSat::lbool ret = solver->solve_with_assumptions(&assumptions);
        assumptions.clear();
        std::fill(is_failed_assumption.begin(), is_failed_assumption.end(), 0);

        if (ret == CMSat::l_True) {
            state = IPASIR2_S_SAT;
            return 10;
        }
        else if (ret == CMSat::l_False) {
            for (CMSat::Lit failed : solver->get_final_conflict()) {
                is_failed_assumption[failed.toInt()] = 1;
            }
            state = IPASIR2_S_UNSAT;
            return 20;
        }
        else if (ret == CMSat::l_Undef) {
            state = IPASIR2_S_INPUT;
            return 0;
        }
        return -1;
    }

    int val(int32_t lit) {
        if (state != IPASIR2_S_SAT) {
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
        if (state != IPASIR2_S_UNSAT) {
            return 0;
        }
        if (is_failed_assumption[toCMSatLit(-lit).toInt()]) {
            return lit;
        }
        return 0;
    }
};


ipasir2_errorcode cms_set_branch_strategy(SolverWrapper* solver, int64_t value) {
    if (solver->getState() != IPASIR2_S_CONFIG) {
        return IPASIR2_E_INVALID_STATE;
    }
    switch (value) {
        case 0: 
            solver->getConf()->branch_strategy_setup.assign("vsids");
            return IPASIR2_E_OK;
        case 1: 
            solver->getConf()->branch_strategy_setup.assign("vmtf");
            return IPASIR2_E_OK;
        case 2: 
            solver->getConf()->branch_strategy_setup.assign("rand");
            return IPASIR2_E_OK;
        case 3: 
            solver->getConf()->branch_strategy_setup.assign("vmtf+vsids");
            return IPASIR2_E_OK;
        default:
            return IPASIR2_E_OPTION_INVALID_VALUE;
    }
}

ipasir2_errorcode cms_set_restart_type(SolverWrapper* solver, int64_t value) {
    if (solver->getState() != IPASIR2_S_CONFIG) {
        return IPASIR2_E_INVALID_STATE;
    }
    solver->getConf()->restartType = CMSat::Restart(value);
    return IPASIR2_E_OK;
}

ipasir2_errorcode cms_set_polarity_mode(SolverWrapper* solver, int64_t value) {
    if (solver->getState() != IPASIR2_S_CONFIG) {
        return IPASIR2_E_INVALID_STATE;
    }
    solver->getConf()->polarity_mode = CMSat::PolarityMode(value);
    return IPASIR2_E_OK;
}

ipasir2_errorcode cms_set_glue_put_lev0_if_below_or_eq(SolverWrapper* solver, int64_t value) {
    if (solver->getState() != IPASIR2_S_CONFIG) {
        return IPASIR2_E_INVALID_STATE;
    }
    solver->getConf()->glue_put_lev0_if_below_or_eq = value;
    return IPASIR2_E_OK;
}

ipasir2_errorcode cms_set_glue_put_lev1_if_below_or_eq(SolverWrapper* solver, int64_t value) {
    if (solver->getState() != IPASIR2_S_CONFIG) {
        return IPASIR2_E_INVALID_STATE;
    }
    solver->getConf()->glue_put_lev1_if_below_or_eq = value;
    return IPASIR2_E_OK;
}

ipasir2_errorcode cms_set_every_lev1_reduce(SolverWrapper* solver, int64_t value) {
    if (solver->getState() != IPASIR2_S_CONFIG) {
        return IPASIR2_E_INVALID_STATE;
    }
    solver->getConf()->every_lev1_reduce = value;
    return IPASIR2_E_OK;
}

ipasir2_errorcode cms_set_every_lev2_reduce(SolverWrapper* solver, int64_t value) {
    if (solver->getState() != IPASIR2_S_CONFIG) {
        return IPASIR2_E_INVALID_STATE;
    }
    solver->getConf()->every_lev2_reduce = value;
    return IPASIR2_E_OK;
}

ipasir2_errorcode cms_set_do_bva(SolverWrapper* solver, int64_t value) {
    if (solver->getState() != IPASIR2_S_CONFIG) {
        return IPASIR2_E_INVALID_STATE;
    }
    solver->getConf()->do_bva = value;
    return IPASIR2_E_OK;
}

ipasir2_errorcode cms_set_do_minim_reduction_more_more(SolverWrapper* solver, int64_t value) {
    if (solver->getState() != IPASIR2_S_CONFIG) {
        return IPASIR2_E_INVALID_STATE;
    }
    solver->getConf()->doMinimRedMoreMore = value;
    return IPASIR2_E_OK;
}

ipasir2_errorcode cms_set_max_num_lits_more_more_red_min(SolverWrapper* solver, int64_t value) {
    if (solver->getState() != IPASIR2_S_CONFIG) {
        return IPASIR2_E_INVALID_STATE;
    }
    solver->getConf()->max_num_lits_more_more_red_min = value;
    return IPASIR2_E_OK;
}

ipasir2_errorcode cms_set_max_glue_more_minim(SolverWrapper* solver, int64_t value) {
    if (solver->getState() != IPASIR2_S_CONFIG) {
        return IPASIR2_E_INVALID_STATE;
    }    
    solver->getConf()->max_glue_more_minim = value;
    return IPASIR2_E_OK;
}

ipasir2_errorcode cms_set_var_elim_ratio_per_iter(SolverWrapper* solver, int64_t value) {
    if (solver->getState() != IPASIR2_S_CONFIG) {
        return IPASIR2_E_INVALID_STATE;    
    }
    solver->getConf()->varElimRatioPerIter = (double)value / 100.0;
    return IPASIR2_E_OK;
}

ipasir2_errorcode cms_set_inc_max_temp_lev2_red_cls(SolverWrapper* solver, int64_t value) {
    if (solver->getState() != IPASIR2_S_CONFIG) {
        return IPASIR2_E_INVALID_STATE;    
    }
    solver->getConf()->inc_max_temp_lev2_red_cls = (double)value / 100.0;
    return IPASIR2_E_OK;
}


extern "C" {

    ipasir2_errorcode ipasir2_signature(const char** signature) {
        static char tmp[200];
        std::string tmp2 = "cryptominisat-";
        tmp2 += CMSat::SATSolver::get_version();
        memcpy(tmp, tmp2.c_str(), tmp2.length()+1);
        *signature = tmp;
        return IPASIR2_E_OK;
    }

    ipasir2_errorcode ipasir2_init(void** solver) {
        *solver = (void*)new SolverWrapper();
        return IPASIR2_E_OK;
    }

    ipasir2_errorcode ipasir2_release(void* solver) {
        delete (SolverWrapper*)solver;
        return IPASIR2_E_OK;
    }

    ipasir2_errorcode ipasir2_options(void* solver, ipasir2_option const** options) {    
        ipasir2_option* solver_options = new ipasir2_option[14];
        solver_options[0] = { "branch_strategy_setup", 0, 3, IPASIR2_S_CONFIG, true, false, (const void*)&cms_set_branch_strategy };
        solver_options[1] = { "varElimRatioPerIter", 10, 100, IPASIR2_S_CONFIG, true, false, (const void*)&cms_set_var_elim_ratio_per_iter }; // %
        solver_options[2] = { "restartType", 0, 4, IPASIR2_S_CONFIG, true, false, (const void*)&cms_set_restart_type };
        solver_options[3] = { "polarity_mode", 0, 7, IPASIR2_S_CONFIG, true, false, (const void*)&cms_set_polarity_mode };
        solver_options[4] = { "inc_max_temp_lev2_red_cls", 4, 100, IPASIR2_S_CONFIG, true, false, (const void*)&cms_set_inc_max_temp_lev2_red_cls }; // %
        solver_options[5] = { "glue_put_lev0_if_below_or_eq", 0, 4, IPASIR2_S_CONFIG, true, false, (const void*)&cms_set_glue_put_lev0_if_below_or_eq };
        solver_options[6] = { "glue_put_lev1_if_below_or_eq", 0, 6, IPASIR2_S_CONFIG, true, false, (const void*)&cms_set_glue_put_lev1_if_below_or_eq };
        solver_options[7] = { "every_lev1_reduce", 1, 10000, IPASIR2_S_CONFIG, true, false, (const void*)&cms_set_every_lev1_reduce };
        solver_options[8] = { "every_lev2_reduce", 1, 15000, IPASIR2_S_CONFIG, true, false, (const void*)&cms_set_every_lev2_reduce };
        solver_options[9] = { "do_bva", 0, 1, IPASIR2_S_CONFIG, true, false, (const void*)&cms_set_do_bva };
        solver_options[10] = { "doMinimRedMoreMore", 0, 2, IPASIR2_S_CONFIG, true, false, (const void*)&cms_set_do_minim_reduction_more_more };
        solver_options[11] = { "max_num_lits_more_more_red_min", 0, 20, IPASIR2_S_CONFIG, true, false, (const void*)&cms_set_max_num_lits_more_more_red_min };
        solver_options[12] = { "max_glue_more_minim", 0, 4, IPASIR2_S_CONFIG, true, false, (const void*)&cms_set_max_glue_more_minim };
        solver_options[13] = { 0 };
        *options = solver_options;
        return IPASIR2_E_OK;
    }

    ipasir2_errorcode ipasir2_set_option(void* solver, ipasir2_option const* opt, int64_t index, int64_t value) {
        if (opt != nullptr && opt->handle != nullptr) {
            void (*setter)(SolverWrapper* solver, int64_t value) = (void (*)(SolverWrapper* solver, int64_t value))opt->handle;
            setter(((SolverWrapper*)solver), value);
            return IPASIR2_E_OK;
        }
        return IPASIR2_E_OPTION_UNKNOWN;
    }

    ipasir2_errorcode ipasir2_add(void* solver, int32_t lit_or_zero) {
        ((SolverWrapper*)solver)->add(lit_or_zero);
        return IPASIR2_E_OK;
    }

    ipasir2_errorcode ipasir2_assume(void* solver, int lit) {
        ((SolverWrapper*)solver)->assume(lit);
        return IPASIR2_E_OK;
    }

    ipasir2_errorcode ipasir2_solve(void* solver, int32_t* status) {
        *status = ((SolverWrapper*)solver)->solve();
        if (*status == -1) {
            return IPASIR2_E_UNKNOWN;
        }
        return IPASIR2_E_OK;
    }

    ipasir2_errorcode ipasir2_val(void* solver, int32_t lit, int32_t* val) {
        *val = ((SolverWrapper*)solver)->val(lit);
        return IPASIR2_E_OK;
    }

    ipasir2_errorcode ipasir2_failed(void* solver, int32_t lit, int32_t* failed) {
        *failed = ((SolverWrapper*)solver)->failed(lit);
        return IPASIR2_E_OK;
    }

    ipasir2_errorcode ipasir2_set_terminate(void* solver, void* state, 
            int (*callback)(void* state)) {
        return IPASIR2_E_UNSUPPORTED;
    }

    ipasir2_errorcode ipasir2_set_export(void* solver, void* state, int32_t max_length,
            void (*callback)(void* state, int32_t const* clause)) {
        return IPASIR2_E_UNSUPPORTED;
    }

    ipasir2_errorcode ipasir2_set_import(void* solver, void* data, ipasir2_redundancy pledge, 
            void (*callback)(void* data, int32_t const** clause, ipasir2_redundancy* type)) {
        return IPASIR2_E_UNSUPPORTED;
    }

    ipasir2_errorcode ipasir2_set_notify(void* solver, void* data, 
            void (*callback)(void* data, int32_t const* assigned, int32_t const* unassigned)) {
        return IPASIR2_E_UNSUPPORTED;
    }

}
