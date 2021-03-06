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

extern DEVICE crdrdr_dev;
extern UNIT crdrdr_unit [N_CRDRDR_UNITS_MAX];

void crdrdr_init(void);
int crdrdr_iom_cmd (uint iomUnitIdx, uint chan);
void crdrdrCardReady (int unitNum);
void rdrProcessEvent (void);

