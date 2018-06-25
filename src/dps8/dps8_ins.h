/*
 Copyright (c) 2007-2013 Michael Mondy
 Copyright 2012-2016 by Harry Reed
 Copyright 2013-2016 by Charles Anthony

 All rights reserved.

 This software is made available under the terms of the
 ICU License -- ICU 1.8.1 and later.
 See the LICENSE file at the top-level directory of this distribution and
 at https://sourceforge.net/p/dps8m/code/ci/master/tree/LICENSE
 */

void tidy_cu (cpu_state_t *cpu_p);
void cu_safe_store(cpu_state_t *cpu_p);
#ifdef MATRIX
void initializeTheMatrix (void);
void addToTheMatrix (uint32 opcode, bool opcodeX, bool a, word6 tag);
t_stat display_the_matrix (int32 arg, const char * buf);
#endif
t_stat prepareComputedAddress (void);   // new
void cu_safe_restore(cpu_state_t *cpu_p);
void fetchInstruction(cpu_state_t *cpu_p, word18 addr);
t_stat executeInstruction (cpu_state_t *cpu_p, bool restart);
void doRCU (cpu_state_t *cpu_p) NO_RETURN;
void traceInstruction (cpu_state_t *cpu_p, uint flag);
bool tstOVFfault (cpu_state_t *cpu_p);
bool chkOVF (cpu_state_t *cpu_p);
