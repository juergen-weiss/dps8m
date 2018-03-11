/*
 Copyright (c) 2007-2013 Michael Mondy
 Copyright 2012-2016 by Harry Reed
 Copyright 2013-2016 by Charles Anthony
 Copyright 2016 by Michal Tomek

 All rights reserved.

 This software is made available under the terms of the
 ICU License -- ICU 1.8.1 and later.
 See the LICENSE file at the top-level directory of this distribution and
 at https://sourceforge.net/p/dps8m/code/ci/master/tree/LICENSE
 */

//#define ISOLTS_BITNO

/**
 * \file dps8_ins.c
 * \project dps8
 * \date 9/22/12
 * \copyright Copyright (c) 2012 Harry Reed. All rights reserved.
*/

#include <stdio.h>

#include "dps8.h"
#include "dps8_cpu.h"
#include "dps8_addrmods.h"
#include "dps8_sys.h"
#include "dps8_faults.h"
#include "dps8_scu.h"
#include "dps8_iom.h"
#include "dps8_cable.h"
#include "dps8_append.h"
#include "dps8_eis.h"
#include "dps8_ins.h"
#include "dps8_math.h"
#include "dps8_opcodetable.h"
#include "dps8_decimal.h"
#include "dps8_iefp.h"
#include "dps8_utils.h"

#define DBG_CTR cpu.cycleCnt

// Forward declarations

static int doABSA (cpu_state_t *cpu_p, word36 * result);
static t_stat doInstruction (cpu_state_t *cpu_p);
#ifdef TESTING
#if EMULATOR_ONLY
static int emCall (void);
#endif
#endif

#ifdef LOOPTRC
#include <time.h>
void timespec_diff(struct timespec *start, struct timespec *stop,
                   struct timespec *result)
{
    if ((stop->tv_nsec - start->tv_nsec) < 0) {
        result->tv_sec = stop->tv_sec - start->tv_sec - 1;
        result->tv_nsec = stop->tv_nsec - start->tv_nsec + 1000000000;
    } else {
        result->tv_sec = stop->tv_sec - start->tv_sec;
        result->tv_nsec = stop->tv_nsec - start->tv_nsec;
    }

    return;
}

void elapsedtime (void)
  {
    static bool init = false;
    static struct timespec t0;
    struct timespec now, delta;

    if (! init)
      {
        init = true;
        clock_gettime (CLOCK_REALTIME, & t0);
      }
    clock_gettime (CLOCK_REALTIME, & now);
    timespec_diff (& t0, & now, & delta);
    sim_printf ("%5ld.%03ld", delta.tv_sec, delta.tv_nsec/1000000);
  }
#endif

// CANFAULT
static void writeOperands (cpu_state_t *cpu_p)
{
    char buf [256];
    CPT (cpt2U, 0); // write operands
    DCDstruct * i = & cpu_p->currentInstruction;

    sim_debug (DBG_ADDRMOD, & cpu_dev,
               "%s (%s):mne=%s flags=%x\n",
               __func__, disassemble (buf, IWB_IRODD), i->info->mne, i->info->flags);

    PNL (cpu_p->prepare_state |= ps_RAW);

    word6 rTAG = 0;
    if (! (i->info->flags & NO_TAG))
      rTAG = GET_TAG (cpu_p->cu.IWB);
    word6 Td = GET_TD (rTAG);
    word6 Tm = GET_TM (rTAG);

//
// IT CI/SC/SCR
//

    if (Tm == TM_IT && (Td == IT_CI || Td == IT_SC || Td == IT_SCR))
      {
        //
        // Put the character into the data word
        //

        switch (cpu_p->ou.characterOperandSize)
          {
            case TB6:
              putChar (& cpu_p->ou.character_data, cpu_p->CY & 077, cpu_p->ou.characterOperandOffset);
              break;

            case TB9:
              putByte (& cpu_p->ou.character_data, cpu_p->CY & 0777, cpu_p->ou.characterOperandOffset);
              break;
          }

        //
        // Write it
        //

        PNL (cpu_p->prepare_state |= ps_SAW);

        Write (cpu_p, cpu_p->ou.character_address, cpu_p->ou.character_data, OPERAND_STORE);

        sim_debug (DBG_ADDRMOD, & cpu_dev,
                   "%s IT wrote char/byte %012"PRIo64" to %06o "
                   "tTB=%o tCF=%o\n",
                   __func__, cpu_p->ou.character_data, cpu_p->ou.character_address,
                   cpu_p->ou.characterOperandSize, cpu_p->ou.characterOperandOffset);

        // Restore the CA; Read/Write() updates it.
        //cpu_p->TPR.CA = indwordAddress;
        cpu_p->TPR.CA = cpu_p->ou.character_address;
        return;
      } // IT

    write_operand (cpu_p, cpu_p->TPR.CA, OPERAND_STORE);

    return;
}

// CANFAULT
static void readOperands (cpu_state_t *cpu_p)
{
    char buf [256];
    CPT (cpt2U, 3); // read operands
    DCDstruct * i = & cpu_p->currentInstruction;

    sim_debug (DBG_ADDRMOD, &cpu_dev,
               "%s (%s):mne=%s flags=%x\n",
               __func__, disassemble (buf, cpu_p->cu.IWB), i->info->mne, i->info->flags);
    sim_debug (DBG_ADDRMOD, &cpu_dev,
              "%s a %d address %08o\n", __func__, i->b29, cpu_p->TPR.CA);

    PNL (cpu_p->prepare_state |= ps_POA);

    word6 rTAG = 0;
    if (! (i->info->flags & NO_TAG))
      rTAG = GET_TAG (cpu_p->cu.IWB);
    word6 Td = GET_TD (rTAG);
    word6 Tm = GET_TM (rTAG);

//
// DU
//

    if (Tm == TM_R && Td == TD_DU)
      {
        cpu_p->CY = 0;
        SETHI (cpu_p->CY, cpu_p->TPR.CA);
        sim_debug (DBG_ADDRMOD, & cpu_dev,
                   "%s DU CY=%012"PRIo64"\n", __func__, cpu_p->CY);
        return;
      }

//
// DL
//

    if (Tm == TM_R && Td == TD_DL)
      {
        cpu_p->CY = 0;
        SETLO (cpu_p->CY, cpu_p->TPR.CA);
        sim_debug (DBG_ADDRMOD, & cpu_dev,
                   "%s DL CY=%012"PRIo64"\n", __func__, cpu_p->CY);
        return;
      }

//
// IT CI/SC/SCR
//

    if (Tm == TM_IT && (Td == IT_CI || Td == IT_SC || Td == IT_SCR))
      {
        //
        // Get the character from the data word
        //

        switch (cpu_p->ou.characterOperandSize)
          {
            case TB6:
              cpu_p->CY = GETCHAR (cpu_p->ou.character_data, cpu_p->ou.characterOperandOffset);
              break;

            case TB9:
              cpu_p->CY = GETBYTE (cpu_p->ou.character_data, cpu_p->ou.characterOperandOffset);
              break;
          }

        sim_debug (DBG_ADDRMOD, & cpu_dev,
                   "%s IT read operand %012"PRIo64" from"
                   " %06o char/byte=%"PRIo64"\n",
                   __func__, cpu_p->ou.character_data, cpu_p->ou.character_address, cpu_p->CY);

        // Restore the CA; Read/Write() updates it.
        cpu_p->TPR.CA = cpu_p->ou.character_address;
        return;
      } // IT

#ifdef LOCKLESS
    read_operand (cpu_p, cpu_p->TPR.CA, ((i->info->flags & RMW) == RMW) ? OPERAND_RMW : OPERAND_READ);
#else
    read_operand (cpu_p, cpu_p->TPR.CA, OPERAND_READ);
#endif

    return;
  }

static void read_tra_op (cpu_state_t *cpu_p)
  {
    Read (cpu_p, cpu_p->TPR.CA, &cpu_p->CY, OPERAND_READ);
    if (! (get_addr_mode (cpu_p) == APPEND_mode || cpu_p->cu.TSN_VALID [0] ||
           cpu_p->cu.XSF /*get_went_appending ()*/))
      {
        if (cpu_p->currentInstruction.info->flags & TSPN_INS)
          {
            word3 n;
            if (cpu_p->currentInstruction.opcode <= 0273)
              n = (cpu_p->currentInstruction.opcode & 3);
            else
              n = (cpu_p->currentInstruction.opcode & 3) + 4;

            // C(PPR.PRR) -> C(PRn.RNR)
            // C(PPR.PSR) -> C(PRn.SNR)
            // C(PPR.IC) -> C(PRn.WORDNO)
            // 000000 -> C(PRn.BITNO)
            cpu_p->PR[n].RNR = cpu_p->PPR.PRR;
// According the AL39, the PSR is 'undefined' in absolute mode.
// ISOLTS thinks means don't change the operand
            if (get_addr_mode (cpu_p) == APPEND_mode)
              cpu_p->PR[n].SNR = cpu_p->PPR.PSR;
            cpu_p->PR[n].WORDNO = (cpu_p->PPR.IC + 1) & MASK18;
            SET_PR_BITNO (n, 0);
            HDBGRegPR (n);
          }
        cpu_p->PPR.IC = cpu_p->TPR.CA;
        // ISOLTS 870-02f
        //cpu_p->PPR.PSR = 0;
      }
    sim_debug (DBG_TRACE, & cpu_dev, "%s %05o:%06o\n",
               __func__, cpu_p->PPR.PSR, cpu_p->PPR.IC);
  }

static void scu2words (cpu_state_t *cpu_p, word36 *words)
  {
    CPT (cpt2U, 6); // scu2words
    memset (words, 0, 8 * sizeof (* words));

    // words[0]

    putbits36_3 (& words[0],  0,  cpu_p->PPR.PRR);
    putbits36_15 (& words[0],  3, cpu_p->PPR.PSR);
    putbits36_1 (& words[0], 18,  cpu_p->PPR.P);
    putbits36_1 (& words[0], 19,  cpu_p->cu.XSF);
    // 20, 1 SDWAMM Match on SDWAM
    putbits36_1 (& words[0], 21,  cpu_p->cu.SD_ON);
    // 22, 1 PTWAMM Match on PTWAM
    putbits36_1 (& words[0], 23,  cpu_p->cu.PT_ON);
#if 0
    putbits36_1 (& words[0], 24,  cpu_p->cu.PI_AP);   // 24    PI-AP
    putbits36_1 (& words[0], 25,  cpu_p->cu.DSPTW);   // 25    DSPTW
    putbits36_1 (& words[0], 26,  cpu_p->cu.SDWNP);   // 26    SDWNP
    putbits36_1 (& words[0], 27,  cpu_p->cu.SDWP);    // 27    SDWP
    putbits36_1 (& words[0], 28,  cpu_p->cu.PTW);     // 28    PTW
    putbits36_1 (& words[0], 29,  cpu_p->cu.PTW2);    // 29    PTW2
    putbits36_1 (& words[0], 30,  cpu_p->cu.FAP);     // 30    FAP
    putbits36_1 (& words[0], 31,  cpu_p->cu.FANP);    // 31    FANP
    putbits36_1 (& words[0], 32,  cpu_p->cu.FABS);    // 32    FABS
#else
    // XXX Only the top 9 bits are used in APUCycleBits, so this is
    // zeroing the 3 FTC bits at the end of the word; on the
    // other hand this keeps the values in apuStatusBits clearer.
    // If FTC is ever used, be sure to put it's save code after this
    // line.
    putbits36_12 (& words[0], 24, cpu_p->cu.APUCycleBits);
#endif

    // words[1]

    putbits36_1 (& words[1],  0, cpu_p->cu.IRO_ISN);
    putbits36_1 (& words[1],  1, cpu_p->cu.OEB_IOC);
    putbits36_1 (& words[1],  2, cpu_p->cu.EOFF_IAIM);
    putbits36_1 (& words[1],  3, cpu_p->cu.ORB_ISP);
    putbits36_1 (& words[1],  4, cpu_p->cu.ROFF_IPR);
    putbits36_1 (& words[1],  5, cpu_p->cu.OWB_NEA);
    putbits36_1 (& words[1],  6, cpu_p->cu.WOFF_OOB);
    putbits36_1 (& words[1],  7, cpu_p->cu.NO_GA);
    putbits36_1 (& words[1],  8, cpu_p->cu.OCB);
    putbits36_1 (& words[1],  9, cpu_p->cu.OCALL);
    putbits36_1 (& words[1], 10, cpu_p->cu.BOC);
    putbits36_1 (& words[1], 11, cpu_p->cu.PTWAM_ER);
    putbits36_1 (& words[1], 12, cpu_p->cu.CRT);
    putbits36_1 (& words[1], 13, cpu_p->cu.RALR);
    putbits36_1 (& words[1], 14, cpu_p->cu.SDWAM_ER);
    putbits36_1 (& words[1], 15, cpu_p->cu.OOSB);
    putbits36_1 (& words[1], 16, cpu_p->cu.PARU);
    putbits36_1 (& words[1], 17, cpu_p->cu.PARL);
    putbits36_1 (& words[1], 18, cpu_p->cu.ONC1);
    putbits36_1 (& words[1], 19, cpu_p->cu.ONC2);
    putbits36_4 (& words[1], 20, cpu_p->cu.IA);
    putbits36_3 (& words[1], 24, cpu_p->cu.IACHN);
    putbits36_3 (& words[1], 27, cpu_p->cu.CNCHN);
    putbits36_5 (& words[1], 30, cpu_p->cu.FI_ADDR);
    putbits36_1 (& words[1], 35, cpu_p->cycle == INTERRUPT_cycle ? 0 : 1);

    // words[2]

    putbits36_3 (& words[2],  0,  cpu_p->TPR.TRR);
    putbits36_15 (& words[2],  3, cpu_p->TPR.TSR);
    // 18, 4 PTWAM levels enabled
    // 22, 4 SDWAM levels enabled
    // 26, 1 0
    putbits36_3 (& words[2], 27, (word3) cpu_p->switches.cpu_num);
    putbits36_6 (& words[2], 30, cpu_p->cu.delta);

    // words[3]

    putbits36_3 (& words[3], 18, cpu_p->cu.TSN_VALID[0] ? cpu_p->cu.TSN_PRNO[0] : 0);
    putbits36_1 (& words[3], 21, cpu_p->cu.TSN_VALID[0]);
    putbits36_3 (& words[3], 22, cpu_p->cu.TSN_VALID[1] ? cpu_p->cu.TSN_PRNO[1] : 0);
    putbits36_1 (& words[3], 25, cpu_p->cu.TSN_VALID[1]);
    putbits36_3 (& words[3], 26, cpu_p->cu.TSN_VALID[2] ? cpu_p->cu.TSN_PRNO[2] : 0);
    putbits36_1 (& words[3], 29, cpu_p->cu.TSN_VALID[2]);
    putbits36_6 (& words[3], 30, cpu_p->TPR.TBR);

    // words[4]

    putbits36_18 (& words[4],  0, cpu_p->PPR.IC);

// According the AL39, the Hex Mode bit should be 0, but ISOLTS pas2 exec checks it; this code does not set it to zero and indicated by AL39.

    putbits36_18 (& words[4], 18, cpu_p->cu.IR);

    // ISOLTS 887 test-03a
    // Adding this makes test03 hang instead of errorign;
    // presumably it's stuck on some later test.
    // An 'Add Delta' addressing mode will alter the TALLY bit;
    // restore it.

    // Breaks ISOLTS 768
    //putbits36_1 (& words[4], 25, cpu_p->currentInstruction.stiTally);

#ifdef ISOLTS
//testing for ipr fault by attempting execution of
//the illegal opcode  000   and bit 27 not set
//in privileged-append-bar mode.
//
//expects ABS to be clear....
//
//testing for ipr fault by attempting execution of
//the illegal opcode  000   and bit 27 not set
//in absolute-bar mode.
//
//expects ABS to be set

//if (cpu_p->PPR.P && TST_I_NBAR == 0) fails 101007 absolute-bar mode; s/b set
//if (cpu_p->PPR.P == 0 && TST_I_NBAR == 0)
//if (TST_I_NBAR == 0 && TST_I_ABS == 1) // If ABS BAR
//{
  //putbits36 (& words[4], 31, 1, 0);
//  putbits36 (& words[4], 31, 1, cpu_p->PPR.P ? 0 : 1);
//if (current_running_cpu_idx)
//sim_printf ("cleared ABS\n");
//}
#endif

    // words[5]

    putbits36 (& words[5],  0, 18, cpu_p->TPR.CA);
    putbits36 (& words[5], 18,  1, cpu_p->cu.repeat_first);
    putbits36 (& words[5], 19,  1, cpu_p->cu.rpt);
    putbits36 (& words[5], 20,  1, cpu_p->cu.rd);
    putbits36 (& words[5], 21,  1, cpu_p->cu.rl);
    putbits36 (& words[5], 22,  1, cpu_p->cu.pot);
    // 23, 1 PON Prepare operand no tally
    putbits36_1 (& words[5], 24, cpu_p->cu.xde);
    putbits36_1 (& words[5], 25, cpu_p->cu.xdo);
    // 26, 1 ITP Execute ITP indirect cycle
    putbits36_1 (& words[5], 27, cpu_p->cu.rfi);
    // 28, 1 ITS Execute ITS indirect cycle
    putbits36_1 (& words[5], 29, cpu_p->cu.FIF);
    putbits36_6 (& words[5], 30, cpu_p->cu.CT_HOLD);

    // words[6]

    words[6] = cpu_p->cu.IWB;

    // words[7]

    words[7] = cpu_p->cu.IRODD;
//sim_printf ("scu2words %lld %012llo\n", cpu_p->cycleCnt, words [6]);
  }


void cu_safe_store (cpu_state_t *cpu_p)
{
    // Save current Control Unit Data in hidden temporary so a later SCU
    // instruction running in FAULT mode can save the state as it existed at
    // the time of the fault rather than as it exists at the time the SCU
    //  instruction is executed.
    scu2words (cpu_p, cpu_p->scu_data);

    cpu_p->cu_data.PSR = cpu_p->PPR.PSR;
    cpu_p->cu_data.PRR = cpu_p->PPR.PRR;
    cpu_p->cu_data.IC =  cpu_p->PPR.IC;

    tidy_cu (cpu_p);

}

void tidy_cu (cpu_state_t *cpu_p)
  {
// The only places this is called is in fault and interrupt processing;
// once the CU is saved, it needs to be set to a usable state. Refactoring
// that code here so that there is only a single copy to maintain.

    cpu_p->cu.delta = 0;
    cpu_p->cu.repeat_first = false;
    cpu_p->cu.rpt = false;
    cpu_p->cu.rd = false;
    cpu_p->cu.rl = false;
    cpu_p->cu.pot = false;
    cpu_p->cu.xde = false;
    cpu_p->cu.xdo = false;
  }

static void words2scu (cpu_state_t *cpu_p, word36 * words)
{
    CPT (cpt2U, 7); // words2scu
    // BUG:  We don't track much of the data that should be tracked

    // words[0]

    cpu_p->PPR.PRR         = getbits36_3  (words[0], 0);
    cpu_p->PPR.PSR         = getbits36_15 (words[0], 3);
    cpu_p->PPR.P           = getbits36_1  (words[0], 18);
    cpu_p->cu.XSF          = getbits36_1  (words[0], 19);
sim_debug (DBG_TRACEEXT, & cpu_dev, "%s sets XSF to %o\n", __func__, cpu_p->cu.XSF);
    //cpu_p->cu.SDWAMM       = getbits36_1  (words[0], 20);
    //cpu_p->cu.SD_ON        = getbits36_1  (words[0], 21);
    //cpu_p->cu.PTWAMM       = getbits36_1  (words[0], 22);
    //cpu_p->cu.PT_ON        = getbits36_1  (words[0], 23);
#if 0
    //cpu_p->cu.PI_AP        = getbits36_1  (words[0], 24);
    //cpu_p->cu.DSPTW        = getbits36_1  (words[0], 25);
    //cpu_p->cu.SDWNP        = getbits36_1  (words[0], 26);
    //cpu_p->cu.SDWP         = getbits36_1  (words[0], 27);
    //cpu_p->cu.PTW          = getbits36_1  (words[0], 28);
    //cpu_p->cu.PTW2         = getbits36_1  (words[0], 29);
    //cpu_p->cu.FAP          = getbits36_1  (words[0], 30);
    //cpu_p->cu.FANP         = getbits36_1  (words[0], 31);
    //cpu_p->cu.FABS         = getbits36_1  (words[0], 32);
#else
    //cpu_p->cu.APUCycleBits = getbits36_12 (words[0], 24);
#endif
    // The FCT is stored in APUCycleBits
    cpu_p->cu.APUCycleBits = (word12) ((cpu_p->cu.APUCycleBits & 07770) | (word12) getbits36_3 (words[0], 33));

    // words[1]

    cpu_p->cu.IRO_ISN      = getbits36_1  (words[1],  0);
    cpu_p->cu.OEB_IOC      = getbits36_1  (words[1],  1);
    cpu_p->cu.EOFF_IAIM    = getbits36_1  (words[1],  2);
    cpu_p->cu.ORB_ISP      = getbits36_1  (words[1],  3);
    cpu_p->cu.ROFF_IPR     = getbits36_1  (words[1],  4);
    cpu_p->cu.OWB_NEA      = getbits36_1  (words[1],  5);
    cpu_p->cu.WOFF_OOB     = getbits36_1  (words[1],  6);
    cpu_p->cu.NO_GA        = getbits36_1  (words[1],  7);
    cpu_p->cu.OCB          = getbits36_1  (words[1],  8);
    cpu_p->cu.OCALL        = getbits36_1  (words[1],  9);
    cpu_p->cu.BOC          = getbits36_1  (words[1], 10);
    cpu_p->cu.PTWAM_ER     = getbits36_1  (words[1], 11);
    cpu_p->cu.CRT          = getbits36_1  (words[1], 12);
    cpu_p->cu.RALR         = getbits36_1  (words[1], 13);
    cpu_p->cu.SDWAM_ER     = getbits36_1  (words[1], 14);
    cpu_p->cu.OOSB         = getbits36_1  (words[1], 15);
    cpu_p->cu.PARU         = getbits36_1  (words[1], 16);
    cpu_p->cu.PARL         = getbits36_1  (words[1], 17);
    cpu_p->cu.ONC1         = getbits36_1  (words[1], 18);
    cpu_p->cu.ONC2         = getbits36_1  (words[1], 19);
    cpu_p->cu.IA           = getbits36_4  (words[1], 20);
    cpu_p->cu.IACHN        = getbits36_3  (words[1], 24);
    cpu_p->cu.CNCHN        = getbits36_3  (words[1], 27);
    cpu_p->cu.FI_ADDR      = getbits36_5  (words[1], 30);
    cpu_p->cu.FLT_INT      = getbits36_1  (words[1], 35);

    // words[2]

    cpu_p->TPR.TRR         = getbits36_3  (words[2], 0);
    cpu_p->TPR.TSR         = getbits36_15 (words[2], 3);
    // 18-21 PTW
    // 22-25 SDW
    // 26 0
    // 27-29 CPU number
    cpu_p->cu.delta        = getbits36_6  (words[2], 30);

    // words[3]

    // 0-17 0

    cpu_p->cu.TSN_PRNO[0]  = getbits36_3  (words[3], 18);
    cpu_p->cu.TSN_VALID[0] = getbits36_1  (words[3], 21);
    cpu_p->cu.TSN_PRNO[1]  = getbits36_3  (words[3], 22);
    cpu_p->cu.TSN_VALID[1] = getbits36_1  (words[3], 25);
    cpu_p->cu.TSN_PRNO[2]  = getbits36_3  (words[3], 26);
    cpu_p->cu.TSN_VALID[2] = getbits36_1  (words[3], 29);
    cpu_p->TPR.TBR         = getbits36_6  (words[3], 30);

    // words[4]

    cpu_p->cu.IR           = getbits36_18 (words[4], 18); // HWR
    cpu_p->PPR.IC          = getbits36_18 (words[4], 0);

    // words[5]

// AL39 pg 75, RCU does not restore CA
    //cpu_p->TPR.CA          = getbits36_18 (words[5], 0);
    cpu_p->cu.repeat_first = getbits36_1  (words[5], 18);
    cpu_p->cu.rpt          = getbits36_1  (words[5], 19);
    cpu_p->cu.rd           = getbits36_1  (words[5], 20);
    cpu_p->cu.rl           = getbits36_1  (words[5], 21);
    cpu_p->cu.pot          = getbits36_1  (words[5], 22);
    // 23 PON
    cpu_p->cu.xde          = getbits36_1  (words[5], 24);
    cpu_p->cu.xdo          = getbits36_1  (words[5], 25);
    // 26 ITP
    cpu_p->cu.rfi          = getbits36_1  (words[5], 27);
    // 28 ITS
    cpu_p->cu.FIF          = getbits36_1  (words[5], 29);
    cpu_p->cu.CT_HOLD      = getbits36_6  (words[5], 30);

    // words[6]

    cpu_p->cu.IWB = words[6];

    // words[7]

    cpu_p->cu.IRODD = words[7];
}

void cu_safe_restore (cpu_state_t *cpu_p)
  {
    words2scu (cpu_p, cpu_p->scu_data);
  }

static void du2words (cpu_state_t *cpu_p, word36 * words)
  {
    CPT (cpt2U, 7); // du2words

#ifdef ISOLTS
    for (int i = 0; i < 8; i ++)
      {
        words[i] = cpu_p->du.image[i];
      }
#else
    memset (words, 0, 8 * sizeof (* words));
#endif
    // Word 0

    putbits36_1  (& words[0],  9, cpu_p->du.Z);
    putbits36_1  (& words[0], 10, cpu_p->du.NOP);
    putbits36_24 (& words[0], 12, cpu_p->du.CHTALLY);

    // Word 1

#ifdef ISOLTS
    words[1] = words[0];
#endif
    // Word 2

    putbits36_18 (& words[2],  0, cpu_p->du.D1_PTR_W);
    putbits36_6  (& words[2], 18, cpu_p->du.D1_PTR_B);
    putbits36_2  (& words[2], 25, cpu_p->du.TAk[0]);
    putbits36_1  (& words[2], 31, cpu_p->du.F1);
    putbits36_1  (& words[2], 32, cpu_p->du.Ak[0]);

    // Word 3

    putbits36_10 (& words[3],  0, cpu_p->du.LEVEL1);
    putbits36_24 (& words[3], 12, cpu_p->du.D1_RES);

    // Word 4

    putbits36_18 (& words[4],  0, cpu_p->du.D2_PTR_W);
    putbits36_6  (& words[4], 18, cpu_p->du.D2_PTR_B);
    putbits36_2  (& words[4], 25, cpu_p->du.TAk[1]);
    putbits36_1  (& words[4], 30, cpu_p->du.R);
    putbits36_1  (& words[4], 31, cpu_p->du.F2);
    putbits36_1  (& words[4], 32, cpu_p->du.Ak[1]);

    // Word 5

    putbits36_10 (& words[5],  0, cpu_p->du.LEVEL2);
    putbits36_24 (& words[5], 12, cpu_p->du.D2_RES);

    // Word 6

    putbits36_18 (& words[6],  0, cpu_p->du.D3_PTR_W);
    putbits36_6  (& words[6], 18, cpu_p->du.D3_PTR_B);
    putbits36_2  (& words[6], 25, cpu_p->du.TAk[2]);
    putbits36_1  (& words[6], 31, cpu_p->du.F3);
    putbits36_1  (& words[6], 32, cpu_p->du.Ak[2]);
    putbits36_3  (& words[6], 33, cpu_p->du.JMP);

    // Word 7

    putbits36_24 (& words[7], 12, cpu_p->du.D3_RES);

  }

static void words2du (cpu_state_t *cpu_p, word36 * words)
  {
    CPT (cpt2U, 8); // words2du
    // Word 0

    cpu_p->du.Z        = getbits36_1  (words[0],  9);
    cpu_p->du.NOP      = getbits36_1  (words[0], 10);
    cpu_p->du.CHTALLY  = getbits36_24 (words[0], 12);
    // Word 1

    // Word 2

    cpu_p->du.D1_PTR_W = getbits36_18 (words[2],  0);
    cpu_p->du.D1_PTR_B = getbits36_6  (words[2], 18);
    cpu_p->du.TAk[0]   = getbits36_2  (words[2], 25);
    cpu_p->du.F1       = getbits36_1  (words[2], 31);
    cpu_p->du.Ak[0]    = getbits36_1  (words[2], 32);

    // Word 3

    cpu_p->du.LEVEL1   = getbits36_10 (words[3],  0);
    cpu_p->du.D1_RES   = getbits36_24 (words[3], 12);

    // Word 4

    cpu_p->du.D2_PTR_W = getbits36_18 (words[4],  0);
    cpu_p->du.D2_PTR_B = getbits36_6  (words[4], 18);
    cpu_p->du.TAk[1]   = getbits36_2  (words[4], 25);
    cpu_p->du.F2       = getbits36_1  (words[4], 31);
    cpu_p->du.Ak[1]    = getbits36_1  (words[4], 32);

    // Word 5

    cpu_p->du.LEVEL2   = getbits36_1  (words[5],  9);
    cpu_p->du.D2_RES   = getbits36_24 (words[5], 12);

    // Word 6

    cpu_p->du.D3_PTR_W = getbits36_18 (words[6],  0);
    cpu_p->du.D3_PTR_B = getbits36_6  (words[6], 18);
    cpu_p->du.TAk[2]   = getbits36_2  (words[6], 25);
    cpu_p->du.F3       = getbits36_1  (words[6], 31);
    cpu_p->du.Ak[2]    = getbits36_1  (words[6], 32);
    cpu_p->du.JMP      = getbits36_3  (words[6], 33);

    // Word 7

    cpu_p->du.D3_RES   = getbits36_24 (words[7], 12);

#ifdef ISOLTS
    for (int i = 0; i < 8; i ++)
      {
        cpu_p->du.image[i] = words[i];
      }
#endif
  }

static char *PRalias[] = {"ap", "ab", "bp", "bb", "lp", "lb", "sp", "sb" };


//=============================================================================

// illegal modifications for various instructions

/*

        00  01  02  03  04  05  06  07

 00     --  au  qu  du  ic  al  ql  dl  R
 10     0   1   2   3   4   5   6   7

 20     n*  au* qu* --  ic* al* al* --  RI
 30     0*  1*  2*  3*  4*  5*  6*  7*

 40     f1  itp --  its sd  scr f2  f3  IT
 50     ci  i   sc  ad  di  dic id  idc

 60     *n  *au *qu --  *ic *al *al --  IR
 70     *0  *1  *2  *3  *4  *5  *6  *7


 bool _allowed[] = {
 // Tm = 0 (register) R
 // --  au     qu     du     ic     al     ql     dl
 true,  false, false, false, false, false, false, false,
 // 0   1      2      3      4      5      6      7
 false, false, false, false, false, false, false, false,
 // Tm = 1 (register then indirect) RI
 // n*  au*    qu*    --     ic*    al*    al*    --
 false, false, false, true,  false, false, false, true,
 // 0*  1*     2*     3*     4*     5*     6*     7*
 false, false, false, false, false, false, false, false,
 // Tm = 2 (indirect then tally) IT
 // f1  itp    --     its    sd     scr    f2     f3
 false, false, true, false, false, false, false, false,
 // ci  i      sc     ad     di     dic    id     idc
 false, false, false, false, false, false, false, false,
 // Tm = 3 (indirect then register) IR
 // *n  *au    *qu    --     *ic    *al    *al    --
 false, false, false, true,  false, false, false, true,
 // *0  *1     *2     *3     *4     *5     *6     *7
 false, false, false, false, false, false, false, false,
 };

 */
// No DUDL

static bool _nodudl[] = {
    // Tm = 0 (register) R
    // --   au     qu     du     ic     al     ql     dl
    false, false, false, true,  false, false, false, true, 
    // 0      1      2      3      4      5      6      7
     false, false, false, false, false, false, false, false,
    // Tm = 1 (register then indirect) RI
    // n*  au*    qu*    --     ic*    al*    al*    --
    false, false, false, true, false, false, false, true, 
    // 0*     1*     2*     3*     4*     5*     6*     7*
    false, false, false, false, false, false, false, false,
    // Tm = 2 (indirect then tally) IT
    // f1  itp    --     its    sd     scr    f2     f3
    false, false, true,  false, false, false, false, false,
    // ci     i      sc     ad     di     dic   id     idc
    false, false, false, false, false, false, false, false,
    // Tm = 3 (indirect then register) IR
    // *n   *au    *qu    --     *ic   *al    *al    --
    false, false, false, true, false, false, false, true, 
    // *0     *1     *2     *3     *4     *5     *6     *7
    false, false, false, false, false, false, false, false,
};

// No DU
// No DL



// (NO_CI | NO_SC | NO_SCR)
static bool _nocss[] = {
    // Tm = 0 (register) R
    // *    au     qu     du     ic     al     ql     dl
    false, false, false, false, false, false, false, false,
    // 0      1      2      3      4      5      6      7
    false, false, false, false, false, false, false, false,
    // Tm = 1 (register then indirect) RI
    // n*  au*    qu*    --     ic*    al*    al*    --
    false, false, false, true, false, false, false, true,
    // 0*     1*     2*     3*     4*     5*     6*     7*
    false, false, false, false, false, false, false, false,
    // Tm = 2 (indirect then tally) IT
    // f1  itp     --     its    sd     scr    f2     f3
    false, false, true,  false, false, true, false, false,
    // ci     i     sc     ad     di    dic    id     idc
    true, false, true, false, false, false, false, false,
    // Tm = 3 (indirect then register) IR
    // *n   *au    *qu    --     *ic   *al    *al    --
    false, false, false, true, false, false, false, true,
    // *0     *1     *2     *3     *4     *5     *6     *7
    false, false, false, false, false, false, false, false,
};

// (NO_DUDL | NO_CISCSCR)
static bool _noddcss[] = {
    // Tm = 0 (register) R
    // *    au     qu     du     ic     al     ql    dl
    false, false, false, true, false, false, false, true,
    // 0      1      2      3      4      5      6      7
    false, false, false, false, false, false, false, false,
    // Tm = 1 (register then indirect) RI
    // n*  au*    qu*    --     ic*    al*    al*    --
    false, false, false, true, false, false, false, true, 
    // 0*     1*     2*     3*     4*     5*     6*     7*
    false, false, false, false, false, false, false, false,
    // Tm = 2 (indirect then tally) IT
    // f1  itp     --     its    sd     scr    f2     f3
    false, false, true,  false, false, true, false, false,
    // ci     i     sc     ad     di    dic    id     idc
    true, false, true, false, false, false, false, false,
    // Tm = 3 (indirect then register) IR
    // *n   *au    *qu    --     *ic   *al    *al    --
    false, false, false, true, false, false, false, true,
    // *0     *1     *2     *3     *4     *5     *6     *7
    false, false, false, false, false, false, false, false,
};

// (NO_DUDL | NO_CISCSCR)
static bool _nodlcss[] = {
    // Tm = 0 (register) R
    // *    au     qu     du      ic     al     ql    dl
    false, false, false, false, false, false, false, true,
    // 0      1      2      3      4      5      6      7
    false, false, false, false, false, false, false, false,
    // Tm = 1 (register then indirect) RI
    // n*  au*    qu*    --     ic*    al*    al*    --
    false, false, false, true, false, false, false, true,
    // 0*     1*     2*     3*     4*     5*     6*     7*
    false, false, false, false, false, false, false, false,
    // Tm = 2 (indirect then tally) IT
    // f1  itp     --     its    sd     scr    f2     f3
    false, false, true,  false, false, true, false, false,
    // ci     i     sc     ad     di    dic    id     idc
    true, false, true, false, false, false, false, false,
    // Tm = 3 (indirect then register) IR
    // *n   *au    *qu    --     *ic   *al    *al    --
    false, false, false, true, false, false, false, true,
    // *0     *1     *2     *3     *4     *5     *6     *7
    false, false, false, false, false, false, false, false,
};

static bool _onlyaqxn[] = {
    // Tm = 0 (register) R
    // --   au     qu     du     ic     al     ql     dl
    false, false, false, true,  true, false, false, true, 
    // 0      1      2      3      4      5      6      7
     false, false, false, false, false, false, false, false,
    // Tm = 1 (register then indirect) RI
    // n*  au*    qu*    --     ic*    al*    al*    --
    false, false, false, true, false, false, false, true, 
    // 0*     1*     2*     3*     4*     5*     6*     7*
    false, false, false, false, false, false, false, false,
    // Tm = 2 (indirect then tally) IT
    // f1  itp    --     its    sd     scr    f2     f3
    false, false, true,  false, false, false, false, false,
    // ci     i      sc     ad     di     dic   id     idc
    false, false, false, false, false, false, false, false,
    // Tm = 3 (indirect then register) IR
    // *n   *au    *qu    --     *ic   *al    *al    --
    false, false, false, true, false, false, false, true, 
    // *0     *1     *2     *3     *4     *5     *6     *7
    false, false, false, false, false, false, false, false,
};

#ifndef QUIET_UNUSED
static bool _illmod[] = {
    // Tm = 0 (register) R
    // *    au     qu     du     ic     al     ql     dl
    false, false, false, false, false, false, false, false,
    // 0      1      2      3      4      5      6      7
    false, false, false, false, false, false, false, false,
    // Tm = 1 (register then indirect) RI
    // n*  au*    qu*    --     ic*    al*    al*    --
    false, false, false, true, false, false, false, true, 
    // 0*     1*     2*     3*     4*     5*     6*     7*
    false, false, false, false, false, false, false, false,
    // Tm = 2 (indirect then tally) IT
    // f1  itp    --     its    sd     scr    f2     f3
    false, false, true,  false, false, false, false, false,
    // ci      i      sc     ad     di     dic   id     idc
    false, false, false, false, false, false, false, false,
    // Tm = 3 (indirect then register) IR
    // *n   *au    *qu    --     *ic   *al    *al    --
    // *0     *1     *2     *3     *4     *5     *6     *7
    false, false, false, true, false, false, false, true,
    false, false, false, false, false, false, false, false,
};
#endif

//=============================================================================

#ifdef MATRIX

static long long theMatrix[1024] // 1024 opcodes (2^10)
                          [2]    // opcode extension
                          [2]    // bit 29
                          [64];  // Tag

void initializeTheMatrix (void)
{
    memset (theMatrix, 0, sizeof (theMatrix));
}

void addToTheMatrix (uint32 opcode, bool opcodeX, bool a, word6 tag)
{
    // safety
    uint _opcode = opcode & 01777;
    int _opcodeX = opcodeX ? 1 : 0;
    int _a = a ? 1 : 0;
    int _tag = tag & 077;
    theMatrix[_opcode][_opcodeX][_a][_tag] ++;
}

t_stat display_the_matrix (UNUSED int32 arg, UNUSED const char * buf)
{
    long long count;

    for (int opcode = 0; opcode < 01000; opcode ++)
    for (int opcodeX = 0; opcodeX < 2; opcodeX ++)
    {
    long long total = 0;
    for (int a = 0; a < 2; a ++)
    for (int tag = 0; tag < 64; tag ++)
    if ((count = theMatrix[opcode][opcodeX][a][tag]))
    {
        // disassemble doesn't quite do what we want so copy the good bits
        static char result[132] = "???";
        strcpy (result, "???");
        // get mnemonic ...
        if (opcodes10 [opcode | (opcodeX ? 01000 : 0)].mne)
          strcpy (result, opcodes10[opcode | (opcodeX ? 01000 : 0)].mne);
        if (a)
            strcat (result, " prn|nnnn");
        else
            strcat (result, " nnnn");

        // get mod
        if (extMods[tag].mod)
        {
            strcat (result, ",");
            strcat (result, extMods[tag].mod);
        }
        if (result[0] == '?')
            sim_printf ("%20"PRId64": ? opcode 0%04o X %d a %d tag 0%02do\n",
                        count, opcode, opcodeX, a, tag);
        else
            sim_printf ("%20"PRId64": %s\n", count, result);
        total += count;
    }
    static char result[132] = "???";
    strcpy (result, "???");
    if (total) {
    // get mnemonic ...
    if (opcodes10 [opcode | (opcodeX ? 01000 : 0)].mne)
      strcpy (result, opcodes10[opcode | (opcodeX ? 01000 : 0)].mne);
    sim_printf ("%20"PRId64": %s\n", total, result);
    }
    }
    return SCPE_OK;
}
#endif


// fetch instrcution at address
// CANFAULT
void fetchInstruction (cpu_state_t *cpu_p, word18 addr)
{
    CPT (cpt2U, 9); // fetchInstruction

    if (get_addr_mode (cpu_p) == ABSOLUTE_mode)
      {
        cpu_p->TPR.TRR = 0;
        cpu_p->RSDWH_R1 = 0;
        //cpu_p->PPR.P = 1; // XXX this should be already set by set_addr_mode, so no worry here
      }

    if (cpu_p->cu.rd && ((cpu_p->PPR.IC & 1) != 0))
      {
        if (cpu_p->cu.repeat_first)
          {
            CPT (cpt2U, 10); // fetch rpt odd
            Read (cpu_p, addr, & cpu_p->cu.IRODD, INSTRUCTION_FETCH);
          }
      }
    else if (cpu_p->cu.rpt || cpu_p->cu.rd || cpu_p->cu.rl)
      {
        if (cpu_p->cu.repeat_first)
          {
            CPT (cpt2U, 11); // fetch rpt even
            Read (cpu_p, addr, & cpu_p->cu.IWB, INSTRUCTION_FETCH);
#if 0
            word36 tmp[2];
            Read2 (cpu_p, addr, tmp, INSTRUCTION_FETCH);
            cpu_p->cu.IWB = tmp[0];
            cpu_p->cu.IRODD = tmp[1];
#endif
          }
      }
    else
      {
        CPT (cpt2U, 12); // fetch 
// ISOLTS test pa870 expects IRODD to be set up.
// If we are fetching an even instruction, also fetch the odd.
// If we are fetching an odd instruction, copy it to IRODD as
// if that was where we got it from.
        //Read (cpu_p, addr, & cpu_p->cu.IWB, INSTRUCTION_FETCH);
        if ((cpu_p->PPR.IC & 1) == 0) // Even
          {
            word36 tmp[2];
            Read2 (cpu_p, addr, tmp, INSTRUCTION_FETCH);
            cpu_p->cu.IWB = tmp[0];
            cpu_p->cu.IRODD = tmp[1];
          }
        else // Odd
          {
            Read (cpu_p, addr, & cpu_p->cu.IWB, INSTRUCTION_FETCH);
            cpu_p->cu.IRODD = cpu_p->cu.IWB; 
          }
      }
}

#ifdef TESTING
void traceInstruction (cpu_state_t *cpu_p, uint flag)
  {
    char buf [256];
    if (! flag) goto force;
    if_sim_debug (flag, &cpu_dev)
      {
force:;
        char * compname;
        word18 compoffset;
        char * where = lookup_address (cpu_p->PPR.PSR, cpu_p->PPR.IC, & compname,
                                       & compoffset);
        bool isBAR = TST_I_NBAR ? false : true;
        if (where)
          {
            if (get_addr_mode (cpu_p) == ABSOLUTE_mode)
              {
                if (isBAR)
                  {
                    sim_debug (flag, &cpu_dev, "%06o|%06o %s\n",
                               cpu_p->BAR.BASE, cpu_p->PPR.IC, where);
                  }
                else
                  {
                    sim_debug (flag, &cpu_dev, "%06o %s\n", cpu_p->PPR.IC, where);
                  }
              }
            else if (get_addr_mode (cpu_p) == APPEND_mode)
              {
                if (isBAR)
                  {
                    sim_debug (flag, &cpu_dev, "%05o:%06o|%06o %s\n",
                               cpu_p->PPR.PSR,
                               cpu_p->BAR.BASE, cpu_p->PPR.IC, where);
                  }
                else
                  {
                    sim_debug (flag, &cpu_dev, "%05o:%06o %s\n",
                               cpu_p->PPR.PSR, cpu_p->PPR.IC, where);
                  }
              }
            list_source (compname, compoffset, flag);
          }
        if (get_addr_mode (cpu_p) == ABSOLUTE_mode)
          {
            if (isBAR)
              {
                sim_debug (flag, &cpu_dev,
                  "%d: "
                  "%05o|%06o %012"PRIo64" (%s) %06o %03o(%d) %o %o %o %02o\n",
                  current_running_cpu_idx,
                  cpu_p->BAR.BASE,
                  cpu_p->PPR.IC,
                  IWB_IRODD,
                  disassemble (buf, IWB_IRODD),
                  cpu_p->currentInstruction.address,
                  cpu_p->currentInstruction.opcode,
                  cpu_p->currentInstruction.opcodeX,
                  cpu_p->currentInstruction.b29,
                  cpu_p->currentInstruction.i,
                  GET_TM (cpu_p->currentInstruction.tag) >> 4,
                  GET_TD (cpu_p->currentInstruction.tag) & 017);
              }
            else
              {
                sim_debug (flag, &cpu_dev,
                  "%d: "
                  "%06o %012"PRIo64" (%s) %06o %03o(%d) %o %o %o %02o\n",
                  current_running_cpu_idx,
                  cpu_p->PPR.IC,
                  IWB_IRODD,
                  disassemble (buf, IWB_IRODD),
                  cpu_p->currentInstruction.address,
                  cpu_p->currentInstruction.opcode,
                  cpu_p->currentInstruction.opcodeX,
                  cpu_p->currentInstruction.b29,
                  cpu_p->currentInstruction.i,
                  GET_TM (cpu_p->currentInstruction.tag) >> 4,
                  GET_TD (cpu_p->currentInstruction.tag) & 017);
              }
          }
        else if (get_addr_mode (cpu_p) == APPEND_mode)
          {
            if (isBAR)
              {
                sim_debug (flag, &cpu_dev,
                  "%d: "
                 "%05o:%06o|%06o %o %012"PRIo64" (%s) %06o %03o(%d) %o %o %o %02o\n",
                  current_running_cpu_idx,
                  cpu_p->PPR.PSR,
                  cpu_p->BAR.BASE,
                  cpu_p->PPR.IC,
                  cpu_p->PPR.PRR,
                  IWB_IRODD,
                  disassemble (buf, IWB_IRODD),
                  cpu_p->currentInstruction.address,
                  cpu_p->currentInstruction.opcode,
                  cpu_p->currentInstruction.opcodeX,
                  cpu_p->currentInstruction.b29, cpu_p->currentInstruction.i,
                  GET_TM (cpu_p->currentInstruction.tag) >> 4,
                  GET_TD (cpu_p->currentInstruction.tag) & 017);
              }
            else
              {
                sim_debug (flag, &cpu_dev,
                  "%d: "
                  "%05o:%06o %o %012"PRIo64" (%s) %06o %03o(%d) %o %o %o %02o\n",
                  current_running_cpu_idx,
                  cpu_p->PPR.PSR,
                  cpu_p->PPR.IC,
                  cpu_p->PPR.PRR,
                  IWB_IRODD,
                  disassemble (buf, IWB_IRODD),
                  cpu_p->currentInstruction.address,
                  cpu_p->currentInstruction.opcode,
                  cpu_p->currentInstruction.opcodeX,
                  cpu_p->currentInstruction.b29,
                  cpu_p->currentInstruction.i,
                  GET_TM (cpu_p->currentInstruction.tag) >> 4,
                  GET_TD (cpu_p->currentInstruction.tag) & 017);
              }
          }
      }

  }
#endif

bool chkOVF (cpu_state_t *cpu_p)
  {
    if (cpu_p->cu.rpt || cpu_p->cu.rd || cpu_p->cu.rl)
      {
        // a:AL39/rpd2
        // Did the repeat instruction inhibit overflow faults?
        if ((cpu_p->rX[0] & 00001) == 0)
          return false;
      }
    return true;
  }
    
bool tstOVFfault (cpu_state_t *cpu_p)
  {
    // Masked?
    if (TST_I_OMASK)
      return false;
    // Doing a RPT/RPD?
    if (cpu_p->cu.rpt || cpu_p->cu.rd || cpu_p->cu.rl)
      {
        // a:AL39/rpd2
        // Did the repeat instruction inhibit overflow faults?
        if ((cpu_p->rX[0] & 00001) == 0)
          return false;
      }
    return true;
  }

t_stat executeInstruction (cpu_state_t *cpu_p)
  {
    CPT (cpt2U, 13); // execute instruction 

//
// Decode the instruction
//
// If not restart
//     if xec/xed
//         check for illegal execute
//     if rpt/rpd
//         check for illegal rpt/rpd modifiers
//     check for illegal modifiers
//     check for privilege
//     initialize CA
//
// Save tally
// Debug trace instruction
// If not restart
//    Initialize TPR
//
// Initialize DU.JMP
// If rpt/rpd
//     If first repeat
//         Initialize Xn
//
// If EIS instruction
//     If not restart
//         Initialize DU.CHTALLY, DU.Z
//     Read operands
//     Parse operands
// Else not EIS instruction
//     If not restart
//         If B29
//             Set TPR from pointer register
//         Else
//             Setup up TPR
//         Initialize CU.CT_HOLD
//     If restart and CU.POT
//         Restore CA from IWB
//     Do CAF if needed
//     Read operand if needed
//
// Execute the instruction
//
// Write operand if needed
// Update IT tally if needed
// If XEC/XED, move instructions into IWB/IRODD
// If instruction was repeated
//     Update Xn
//     Check for repeat termination
// Post-instruction debug


///
/// executeInstruction: Decode the instruction
///

    DCDstruct * ci = & cpu_p->currentInstruction;
    decode_instruction (cpu_p, IWB_IRODD, ci);
    //cpu_p->isb29 = ci->b29;
    //ISB29 = ci->b29;
    const struct opcode_s *info = ci->info;

// Local caches of frequently accessed data

    const uint ndes = info->ndes;
    const bool restart = ci->restart;         // instruction is to be restarted
    const opc_flag flags = info->flags;
    const opc_mod mods = info->mods;
    const uint32 opcode = ci->opcode;   // opcode
    const bool opcodeX = ci->opcodeX;  // opcode extension
    const word6 tag = ci->tag;          // instruction tag


#ifdef MATRIX
    {
      const uint32  opcode = ci->opcode;   // opcode
      const bool   opcodeX = ci->opcodeX;  // opcode extension
                                           // XXX replace with rY
      const bool   b29 = ci->b29;              // bit-29 - addressing via pointer
                                           // register
      const word6  tag = ci->tag;          // instruction tag
                                           //  XXX replace withrTAG
      addToTheMatrix (opcode, opcodeX, b29, tag);
    }
#endif

//#define likely(x) (x)
//#define unlikely(x) (x)
#define likely(x) __builtin_expect ((x), 1)
#define unlikely(x) __builtin_expect ((x), 0)

//sim_debug (DBG_TRACEEXT, & cpu_dev, "isb29 %o\n", ci->b29);
    if (ci->b29)
      ci->address = SIGNEXT15_18 (ci->address & MASK15);

#ifdef L68
    CPTUR (cptUseMR);
    if (unlikely (cpu_p->MR.emr && cpu_p->MR.OC_TRAP))
      {
        if (cpu_p->MR.OPCODE == opcode &&
            cpu_p->MR.OPCODEX == opcodeX) 
          {
            if (cpu_p->MR.ihrrs)
              {
                cpu_p->MR.ihr = 0;
              }
            CPT (cpt2U, 14); // opcode trap
            //set_FFV_fault (2); // XXX According to AL39
            do_FFV_fault (1, "OC TRAP");
          }
      }
#endif // L68

///
/// executeInstruction: Non-restart processing
///

    if (likely (!restart) || unlikely (ndes > 0)) // until we implement EIS restart
    {
        cpu_p->cu.TSN_VALID[0] = 0;
        cpu_p->cu.TSN_VALID[1] = 0;
        cpu_p->cu.TSN_VALID[2] = 0;
        cpu_p->cu.TSN_PRNO[0] = 0;
        cpu_p->cu.TSN_PRNO[1] = 0;
        cpu_p->cu.TSN_PRNO[2] = 0;
    }

    if (unlikely (restart))
      goto restart_1;

//
// not restart
//

    cpu_p->cu.XSF = 0;
sim_debug (DBG_TRACEEXT, & cpu_dev, "%s sets XSF to %o\n", __func__, cpu_p->cu.XSF);

    CPT (cpt2U, 14); // non-restart processing
    // Set Address register empty
    PNL (L68_ (cpu_p->AR_F_E = false;))

    // Reset the fault counter
    cpu_p->cu.APUCycleBits &= 07770;

    //cpu_p->cu.TSN_VALID[0] = 0;
    //cpu_p->cu.TSN_VALID[1] = 0;
    //cpu_p->cu.TSN_VALID[2] = 0;

    // If executing the target of XEC/XED, check the instruction is allowed
    if (unlikely (cpu_p->isXED))
      {
        if (flags & NO_XED)
            doFault (cpu_p, FAULT_IPR,
                     fst_ill_proc,
                     "Instruction not allowed in XEC/XED");
        // The even instruction from C(Y-pair) must not alter
        // C(Y-pair)36,71, and must not be another xed instruction.
        if (opcode == 0717 && !opcodeX && cpu_p->cu.xdo /* even instruction being executed */)
            doFault (cpu_p, FAULT_IPR,
                     fst_ill_proc,
                     "XED of XED on even word");
        // ISOLTS 791 03k, 792 03k
        if (opcode == 0560 && !opcodeX) {
            // To Execute Double (XED) the RPD instruction, the RPD must be the second
            // instruction at an odd-numbered address.
            if (cpu_p->cu.xdo /* even instr being executed */)
                doFault (cpu_p, FAULT_IPR,
                     (_fault_subtype) {.fault_ipr_subtype=FR_ILL_PROC},
                     "XED of RPD on even word");
            // To execute an instruction pair having an rpd instruction as the odd
            // instruction, the xed instruction must be located at an odd address.
            if (!cpu_p->cu.xdo /* odd instr being executed */ && !(cpu_p->PPR.IC & 1))
                doFault (cpu_p, FAULT_IPR,
                     (_fault_subtype) {.fault_ipr_subtype=FR_ILL_PROC},
                     "XED of RPD on odd word, even IC");
        }
    } else if (unlikely (cpu_p->isExec)) {
        // To execute a rpd instruction, the xec instruction must be in an odd location.
        // ISOLTS 768 01w
        if (opcode == 0560 && !opcodeX && !cpu_p->cu.xde && !(cpu_p->PPR.IC & 1)) 
            doFault (cpu_p, FAULT_IPR,
                 (_fault_subtype) {.fault_ipr_subtype=FR_ILL_PROC},
                 "XEC of RPx on even word");
    }

    // ISOLTS wants both the not allowed in RPx and RPx illegal modifier 
    // tested.
    fault_ipr_subtype_ RPx_fault = 0;

    // In BAR mode and not allowed?

#if 0
    if (TST_I_NBAR == 0)
      if (flags & NO_BAR)
        RPx_fault |= FR_ILL_SLV;
#endif

    // RPT/RPD illegal modifiers
    // a:AL39/rpd3
    if (unlikely (cpu_p->cu.rpt || cpu_p->cu.rd || cpu_p->cu.rl))
      {
        if (! (flags & NO_TAG))
          {
            // check for illegal modifiers:
            //    only R & RI are allowed
            //    only X1..X7
            switch (GET_TM (tag))
              {
                case TM_RI:
                  if (cpu_p->cu.rl)
                    {
                      RPx_fault |= FR_ILL_MOD;
                    }
                  break;
                case TM_R:
                  break;
                default:
                  // generate fault. Only R & RI allowed
                  RPx_fault |= FR_ILL_MOD;
              }

            word6 Td = GET_TD (tag);
            if (Td == TD_X0)
              {
                RPx_fault |= FR_ILL_MOD;
              }
            //if (! cpu_p->cu.rd && Td < TD_X0)
            if (Td < TD_X0)
              {
                RPx_fault |= FR_ILL_MOD;
              }
          }

#ifdef DPS8M
        // ISOLTS 792 03e
        // this is really strange. possibly a bug in DPS8M HW (L68 handles it the same as all other instructions)
        if (RPx_fault && !opcodeX && opcode==0413) // rscr
          {
              doFault (cpu_p, FAULT_IPR,
                 (_fault_subtype) {.fault_ipr_subtype=RPx_fault},
                 "DPS8M rscr early raise");
          }
#endif

    // Instruction not allowed in RPx?

    if (unlikely (cpu_p->cu.rpt || cpu_p->cu.rd || cpu_p->cu.rl))
      {
        if (flags & NO_RPT)
          {
            RPx_fault |= FR_ILL_PROC;
          }
      }

    if (unlikely (cpu_p->cu.rl))
      {
        if (flags & NO_RPL)
          {
            RPx_fault |= FR_ILL_PROC;
          }
      }

#ifdef L68
        // ISOLTS 791 03d, 792 03d
        // L68 wants ILL_MOD here - stca,stcq,stba,stbq,scpr,lcpr
        // all these instructions have a nonstandard TAG field interpretation. probably a HW bug in decoder
        if (RPx_fault && !opcodeX && (opcode==0751 || opcode==0752 || opcode==0551 
            || opcode==0552 || opcode==0452 || opcode==0674))
          {
            RPx_fault |= FR_ILL_MOD;
          }
#endif
      }

    if (unlikely (RPx_fault))
      {
        doFault (cpu_p, FAULT_IPR,
                 (_fault_subtype) {.fault_ipr_subtype=RPx_fault},
                 "RPx test fail");
      }

    ///                     check for illegal addressing mode(s) ...
    ///
    // ISOLTS wants both the IPR and illegal modifier tested.
    fault_ipr_subtype_ mod_fault = 0;

    // No CI/SC/SCR allowed
    if (mods == NO_CSS)
    {
        if (_nocss[tag])
            mod_fault |= FR_ILL_MOD; // "Illegal CI/SC/SCR modification"
    }
    // No DU/DL/CI/SC/SCR allowed
    else if (mods == NO_DDCSS)
    {
        if (_noddcss[tag])
            mod_fault |= FR_ILL_MOD; // "Illegal DU/DL/CI/SC/SCR modification"
    }
    // No DL/CI/SC/SCR allowed
    else if (mods == NO_DLCSS)
    {
        if (_nodlcss[tag])
            mod_fault |= FR_ILL_MOD; // "Illegal DL/CI/SC/SCR modification"
    }
    // No DU/DL allowed
    else if (mods == NO_DUDL)
    {
        if (_nodudl[tag])
            mod_fault |= FR_ILL_MOD; // "Illegal DU/DL modification"
    }
    else if (mods == ONLY_AU_QU_AL_QL_XN)
    {
        if (_onlyaqxn[tag])
            mod_fault |= FR_ILL_MOD; // "Illegal DU/DL/IC modification"
    }

#ifdef L68
    // L68 raises it immediately
    if (mod_fault)
      {
        doFault (cpu_p, FAULT_IPR,
                 (_fault_subtype) {.fault_ipr_subtype=mod_fault},
                 "Illegal modifier");
      }
#endif

    // check for priv ins - Attempted execution in normal or BAR modes causes a
    // illegal procedure fault.
    if (unlikely (flags & PRIV_INS))
      {
#ifdef DPS8M
        // DPS8M illegal instructions lptp,lptr,lsdp,lsdr
        // ISOLTS 890 05abc
        if (((opcode == 0232 || opcode == 0173) && opcodeX ) 
           || (opcode == 0257))
        {
            doFault (cpu_p, FAULT_IPR,
                (_fault_subtype) {.fault_ipr_subtype=FR_ILL_OP|mod_fault},
                "Attempted execution of multics privileged instruction.");
        }
#endif
        if (!is_priv_mode (cpu_p))
          {
            // "multics" privileged instructions: absa,ldbr,lra,rcu,scu,sdbr,ssdp,ssdr,sptp,sptr
            // ISOLTS 890 05abc,06abc
#ifdef DPS8M
            if (((opcode == 0212 || opcode == 0232 || opcode == 0613 || opcode == 0657) && !opcodeX )
               || ((opcode == 0254 || opcode == 0774) && opcodeX ) 
               || (opcode == 0557 || opcode == 0154))
#else // L68
            // on L68, lptp,lptr,lsdp,lsdr instructions are not illegal, so handle them here
            if (((opcode == 0212 || opcode == 0232 || opcode == 0613 || opcode == 0657) && !opcodeX )
               || ((opcode == 0254 || opcode == 0774 || opcode == 0232 || opcode == 0173) && opcodeX ) 
               || (opcode == 0557 || opcode == 0154 || opcode == 0257))
#endif
            {
                if (!get_bar_mode (cpu_p)) {
                    // ISOLTS-890 05ab
                    doFault (cpu_p, FAULT_IPR,
                        (_fault_subtype) {.fault_ipr_subtype=FR_ILL_SLV|mod_fault},
                        "Attempted execution of multics privileged instruction.");
                } else {
                    doFault (cpu_p, FAULT_IPR,
                        (_fault_subtype) {.fault_ipr_subtype=FR_ILL_OP|mod_fault},
                        "Attempted execution of multics privileged instruction.");
                }
            }
            doFault (cpu_p, FAULT_IPR,
                (_fault_subtype) {.fault_ipr_subtype=FR_ILL_SLV|mod_fault},
                "Attempted execution of privileged instruction.");
          }
      }

    if (unlikely (flags & NO_BAR))
      if (get_bar_mode(cpu_p))
        {
          // lbar
          // ISOLTS 890 06a
          // ISOLTS says that L68 handles this in the same way
          if (opcode == 0230 && !opcodeX) {
            doFault (cpu_p, FAULT_IPR,
                (_fault_subtype) {.fault_ipr_subtype=FR_ILL_SLV|mod_fault},
                "Attempted BAR execution of nonprivileged instruction.");
          } else
            doFault (cpu_p, FAULT_IPR,
                (_fault_subtype) {.fault_ipr_subtype=FR_ILL_OP|mod_fault},
                "Attempted BAR execution of nonprivileged instruction.");
      }

#ifdef DPS8M
    // DPS8M raises it delayed
    if (unlikely (mod_fault))
      {
        doFault (cpu_p, FAULT_IPR,
                 (_fault_subtype) {.fault_ipr_subtype=mod_fault},
                 "Illegal modifier");
      }
#endif

    ///
    /// executeInstruction: Restart or Non-restart processing
    ///                     Initialize address registers
    ///
restart_1:

#if 0 // #ifndef CA_REWORK
#if 1
    cpu_p->TPR.CA = ci->address;
    cpu_p->iefpFinalAddress = cpu_p->TPR.CA;
    //cpu_p->rY = cpu_p->TPR.CA;
#else
    cpu_p->iefpFinalAddress = ci->address;
    cpu_p->rY = ci->address;
#endif
#endif



    CPT (cpt2U, 15); // instruction processing
///
/// executeInstruction: Initialize state saving registers
///

    // XXX this may be wrong; make sure that the right value is used
    // if a page fault occurs. (i.e. this may belong above restart_1.
    // This is also used by the SCU instruction. ISOLTS tst887 does
    // a 'SCU n,ad' with a tally of 1; the tally is decremented, setting
    // the IR tally bit as part of the CA calculation; this is not
    // the machine conditions that the SCU instruction is saving.

    ci->stiTally = TST_I_TALLY;   // for sti instruction

///
/// executeInstruction: simh hooks
///

#ifndef SPEED
    // Don't trace Multics idle loop
    //if (cpu_p->PPR.PSR != 061 || cpu_p->PPR.IC != 0307)

      {
        traceInstruction (DBG_TRACE);
#ifdef HDBG
        hdbgTrace ();
#endif // HDBG
      }
#else  // !SPEED
#ifdef HDBG
    // Don't trace Multics idle loop
    //if (cpu_p->PPR.PSR != 061 || cpu_p->PPR.IC != 0307)
      hdbgTrace ();
#endif // HDBG
#endif // !SPEED

///
/// executeInstruction: Initialize misc.
///

    cpu_p->du.JMP = (word3) ndes;
    cpu_p->dlyFlt = false;

///
/// executeInstruction: RPT/RPD/RPL special processing for 'first time'
///

    if (unlikely (cpu_p->cu.rpt || cpu_p->cu.rd || cpu_p->cu.rl))
      {
        CPT (cpt2U, 15); // RPx processing
//
// RPT:
//
// The computed address, y, of the operand (in the case of R modification) or
// indirect word (in the case of RI modification) is determined as follows:
//
// For the first execution of the repeated instruction:
//      C(C(PPR.IC)+1)0,17 + C(Xn) -> y, y -> C(Xn)
//
// For all successive executions of the repeated instruction:
//      C(Xn) + Delta -> y, y -> C(Xn);
//
//
// RPD:
//
// The computed addresses, y-even and y-odd, of the operands (in the case of
// R modification) or indirect words (in the case of RI modification) are
// determined as follows:
//
// For the first execution of the repeated instruction pair:
//      C(C(PPR.IC)+1)0,17 + C(X-even) -> y-even, y-even -> C(X-even)
//      C(C(PPR.IC)+2)0,17 + C(X-odd) -> y-odd, y-odd -> C(X-odd)
//
// For all successive executions of the repeated instruction pair:
//      if C(X0)8 = 1, then C(X-even) + Delta -> y-even,
//           y-even -> C(X-even);
//      otherwise, C(X-even) -> y-even
//      if C(X0)9 = 1, then C(X-odd) + Delta -> y-odd,
//           y-odd -> C(X-odd);
//      otherwise, C(X-odd) -> y-odd
//
// C(X0)8,9 correspond to control bits A and B, respectively, of the rpd
// instruction word.
//
//
// RL:
//
// The computed address, y, of the operand is determined as follows:
//
// For the first execution of the repeated instruction:
//
//      C(C(PPR.IC)+1)0,17 + C(Xn) -> y, y -> C(Xn)
//
// For all successive executions of the repeated instruction:
//
//      C(Xn) -> y
//
//      if C(Y)0,17 != 0, then C (y)0,17 -> C(Xn);
//
//      otherwise, no change to C(Xn)
//
//  C(Y)0,17 is known as the link address and is the computed address of the
//  next entry in a threaded list of operands to be referenced by the repeated
//  instruction.
//

        sim_debug (DBG_TRACEEXT, & cpu_dev,
                   "RPT/RPD first %d rpt %d rd %d e/o %d X0 %06o a %d b %d\n",
                   cpu_p->cu.repeat_first, cpu_p->cu.rpt, cpu_p->cu.rd, cpu_p->PPR.IC & 1,
                   cpu_p->rX[0], !! (cpu_p->rX[0] & 01000), !! (cpu_p->rX[0] & 0400));
        sim_debug (DBG_TRACEEXT, & cpu_dev,
                   "RPT/RPD CA %06o\n", cpu_p->TPR.CA);

// Handle first time of a RPT or RPD

        if (cpu_p->cu.repeat_first)
          {
            CPT (cpt2U, 16); // RPx first processing
            // The semantics of these are that even is the first instruction of
            // and RPD, and odd the second.

            bool icOdd = !! (cpu_p->PPR.IC & 1);
            bool icEven = ! icOdd;

            // If RPT or (RPD and the odd instruction)
            if (cpu_p->cu.rpt || (cpu_p->cu.rd && icOdd) || cpu_p->cu.rl)
              cpu_p->cu.repeat_first = false;

            // a:RJ78/rpd6
            // For the first execution of the repeated instruction:
            // C(C(PPR.IC)+1)0,17 + C(Xn) -> y, y -> C(Xn)
            if (cpu_p->cu.rpt ||              // rpt
                (cpu_p->cu.rd && icEven) ||   // rpd & even
                (cpu_p->cu.rd && icOdd)  ||   // rpd & odd
                cpu_p->cu.rl)                 // rl
              {
#if 0
                word18 offset;
                if (ci->b29)
                  {
{ static bool first = true;
if (first) {
first = false;
sim_printf ("XXX rethink this; bit 29 is finagled below; should this be done in a different order?\n");
}}
sim_debug (DBG_TRACEEXT, & cpu_dev, "b29, ci->address %o\n", ci->address);
                    // a:RJ78/rpd4
                    offset = SIGNEXT15_18 (ci->address & MASK15);
                  }
                else
                  offset = ci->address;
#else
                word18 offset = ci->address;
#endif
                offset &= AMASK;

                sim_debug (DBG_TRACEEXT, & cpu_dev,
                           "rpt/rd/rl repeat first; offset is %06o\n", offset);

                word6 Td = GET_TD (tag);
                uint Xn = X (Td);  // Get Xn of next instruction
                sim_debug (DBG_TRACEEXT, & cpu_dev,
                           "rpt/rd/rl repeat first; X%d was %06o\n",
                           Xn, cpu_p->rX[Xn]);
                // a:RJ78/rpd5
                cpu_p->TPR.CA = (cpu_p->rX[Xn] + offset) & AMASK;
                cpu_p->rX[Xn] = cpu_p->TPR.CA;
                HDBGRegX (Xn);
                sim_debug (DBG_TRACEEXT, & cpu_dev,
                           "rpt/rd/rl repeat first; X%d now %06o\n",
                           Xn, cpu_p->rX[Xn]);
              } // rpt or rd or rl

          } // repeat first
      } // cpu_p->cu.rpt || cpu_p->cu.rd || cpu_p->cu.rl

///
/// Restart or Non-restart
///

///
/// executeInstruction: EIS operand processing
///

    if (unlikely (ndes > 0))
      {
        CPT (cpt2U, 27); // EIS operand processing
        sim_debug (DBG_APPENDING, &cpu_dev, "initialize EIS descriptors\n");
        // This must not happen on instruction restart
        if (!restart)
          {
            CPT (cpt2U, 28); // EIS not restart
            cpu_p->du.CHTALLY = 0;
            cpu_p->du.Z = 1;
          }
        for (uint n = 0; n < ndes; n += 1)
          {
            CPT (cpt2U, 29 + n); // EIS operand fetch (29, 30, 31)
// XXX This is a bit of a hack; In general the code is good about
// setting up for bit29 or PR operations by setting up TPR, but
// assumes that the 'else' case can be ignored when it should set
// TPR to the canonical values. Here, in the case of a EIS instruction
// restart after page fault, the TPR is in an unknown state. Ultimately,
// this should not be an issue, as this folderol would be in the DU, and
// we would not be re-executing that code, but until then, set the TPR
// to the condition we know it should be in.
            cpu_p->TPR.TRR = cpu_p->PPR.PRR;
            cpu_p->TPR.TSR = cpu_p->PPR.PSR;
#if 0
{ static bool first = true;
if (first) {
first = false;
sim_printf ("XXX this had b29 of 0; it may be necessary to clear TSN_VALID[0]\n");
}}
#else
            //Read (cpu_p, cpu_p->PPR.IC + 1 + n, & cpu_p->currentEISinstruction.op[n],
                  //INSTRUCTION_FETCH);
            Read (cpu_p, cpu_p->PPR.IC + 1 + n, & cpu_p->currentEISinstruction.op[n],
                  APU_DATA_READ);
#endif
          }
        PNL (cpu_p->IWRAddr = cpu_p->currentEISinstruction.op[0]);
        setupEISoperands ();
      }

///
/// Restart or Non-restart
///

///
/// executeInstruction: non-EIS operand processing
///

    else
      {
        CPT (cpt2U, 32); // non-EIS operand processing
        CPT (cpt2U, 33); // not restart non-EIS operand processing
        if (ci->b29)   // if A bit set set-up TPR stuff ...
          {
            CPT (cpt2U, 34); // B29

// AL39 says that RCU does not restore CA, so words to SCU does not.
// So we do it here, even if restart
            word3 n = GET_PRN(IWB_IRODD);  // get PRn
            word15 offset = GET_OFFSET(IWB_IRODD);
            CPTUR (cptUsePRn + n);

            sim_debug (DBG_APPENDING, &cpu_dev,
                       "doPtrReg: PR[%o] SNR=%05o RNR=%o WORDNO=%06o "
                       "BITNO=%02o\n",
                       n, cpu_p->PAR[n].SNR, cpu_p->PAR[n].RNR,
                       cpu_p->PAR[n].WORDNO, GET_PR_BITNO (n));

#if 0 // #ifndef CA_REWORK
            cpu_p->TPR.CA = (cpu_p->PAR[n].WORDNO + SIGNEXT15_18 (offset))
                         & MASK18;
#endif

// Fix tst880: 'call6 pr1|0'. The instruction does a DF1; the fault handler
// updates PRR in the CU save data. On restart, TRR is not updated. 
// Removing the 'if' appears to resolve the problem without regressions.
            //if (!restart)
              {
// Not EIS, bit 29 set, !restart
                cpu_p->TPR.TBR = GET_PR_BITNO (n);

                cpu_p->TPR.TSR = cpu_p->PAR[n].SNR;
                cpu_p->TPR.TRR = max3 (cpu_p->PAR[n].RNR, cpu_p->TPR.TRR, cpu_p->PPR.PRR);

                sim_debug (DBG_APPENDING, &cpu_dev,
                           "doPtrReg: n=%o offset=%05o TPR.CA=%06o "
                           "TPR.TBR=%o TPR.TSR=%05o TPR.TRR=%o\n",
                           n, offset, cpu_p->TPR.CA, cpu_p->TPR.TBR, 
                           cpu_p->TPR.TSR, cpu_p->TPR.TRR);
                cpu_p->cu.XSF = 1;
sim_debug (DBG_TRACEEXT, & cpu_dev, "executeInstruction !restart !EIS sets XSF to %o\n", cpu_p->cu.XSF);
                //set_went_appending ();
            }

// Putting the a29 clear here makes sense, but breaks the emulator for unclear
// reasons (possibly ABSA?). Do it in updateIWB instead
//                ci->a = false;
//                // Don't clear a; it is needed to detect change to appending
//                //  mode
//                //a = false;
//                putbits36_1 (& cpu_p->cu.IWB, 29, 0);
          }
        else
          {
// not eis, not bit b29
            if (!restart)
              {
                CPT (cpt2U, 35); // not B29
                cpu_p->cu.TSN_VALID [0] = 0;
                cpu_p->TPR.TBR = 0;
                if (get_addr_mode (cpu_p) == ABSOLUTE_mode)
                  {
                    cpu_p->TPR.TSR = cpu_p->PPR.PSR;
                    cpu_p->TPR.TRR = 0;
                    cpu_p->RSDWH_R1 = 0;
                  }
                cpu_p->cu.XSF = 0;
sim_debug (DBG_TRACEEXT, & cpu_dev, "executeInstruction not EIS sets XSF to %o\n", cpu_p->cu.XSF);
                //clr_went_appending ();
              }
          }

        // This must not happen on instruction restart
        if (!restart)
          {
            cpu_p->cu.CT_HOLD = 0; // Clear interrupted IR mode flag
          }


#if 0 // #ifndef CA_REWORK
        //
        // If POT is set, a page fault occured during the fetch of the data word
        // pointed to by an indirect addressing word, and the saved CA points
        // to the data word instead of the indirect word; reset the CA correctly
        //

        if (restart && cpu_p->cu.pot)
          {
            CPT (cpt2L, 0); // POT set
            cpu_p->TPR.CA = GET_ADDR (IWB_IRODD);
            if (getbits36_1 (cpu_p->cu.IWB, 29) != 0)
              cpu_p->TPR.CA &= MASK15;
          }
#endif

        // These are set by do_caf
        cpu_p->ou.directOperandFlag = false;
        cpu_p->ou.directOperand = 0;
        cpu_p->ou.characterOperandSize = 0;
        cpu_p->ou.characterOperandOffset = 0;
        cpu_p->ou.crflag = false;

#define REORDER
#ifdef REORDER
        if ((flags & PREPARE_CA) || WRITEOP (ci) || READOP (ci))
          {
            CPT (cpt2L, 1); // CAF
            do_caf (cpu_p);
            PNL (L68_ (cpu_p->AR_F_E = true;))
            cpu_p->iefpFinalAddress = cpu_p->TPR.CA;
          }

        //if (READOP (ci) && ! ((bool) (flags & TRANSFER_INS)))
        if (READOP (ci))
          {
            CPT (cpt2L, 2); // Read operands
            readOperands (cpu_p);
            if (cpu_p->cu.rl)
              {
                switch (operand_size (cpu_p))
                  {
                    case 1:
                      {
                        cpu_p->lnk = GETHI36 (cpu_p->CY);
                        cpu_p->CY &= MASK18;
                        break;
                      }
                    case 2:
                      {
                        cpu_p->lnk = GETHI36 (cpu_p->Ypair[0]);
                        cpu_p->Ypair[0] &= MASK18;
                        break;
                      }
                    default:
                      {
                        break;
                      }
                  }
              }
          }
#else
        if (flags & PREPARE_CA)
          {
            do_caf ();
            L68_ (cpu_p->AR_F_E = true;)
            cpu_p->iefpFinalAddress = cpu_p->TPR.CA;
          }
        else if (READOP (ci))
          {
            do_caf ();
            cpu_p->iefpFinalAddress = cpu_p->TPR.CA;
            readOperands ();
          }
#endif
        PNL (cpu_p->IWRAddr = 0);
      }

// Initiialize zone to 'entire word'

    cpu_p->useZone = false;
    cpu_p->zone = MASK36;

///
/// executeInstruction: Execute the instruction
///

    t_stat ret = doInstruction (cpu_p);

///
/// executeInstruction: Write operand
///

    if (WRITEOP (ci))
      {
        CPT (cpt2L, 3); // Write operands
#ifndef REORDER
        if (! READOP (ci))
          {
            do_caf ();
            cpu_p->iefpFinalAddress = cpu_p->TPR.CA;
          }
#endif
#ifdef LOCKLESS
	if ((ci->info->flags & RMW) == RMW)
	  {
	      if (operand_size(cpu_p) != 1)
		  sim_warn("executeInstruction: operand_size!= 1\n");
	      core_write_unlock (cpu_p, cpu_p->iefpFinalAddress, cpu_p->CY, __func__);
         }
	else
	  writeOperands (cpu_p);
#else
        writeOperands (cpu_p);
#endif
      }

    else if (flags & PREPARE_CA)
      {
        // 'EPP ITS; TRA' confuses the APU by leaving last_cycle 
        // at INDIRECT_WORD_FETCH; defoobarize the APU:
        fauxDoAppendCycle (cpu_p, OPERAND_READ);
        cpu_p->TPR.TRR = cpu_p->PPR.PRR;
        cpu_p->TPR.TSR = cpu_p->PPR.PSR;
        cpu_p->TPR.TBR = 0;
      }

///
/// executeInstruction: RPT/RPD/RPL processing
///


    // The semantics of these are that even is the first instruction of
    // and RPD, and odd the second.

    bool icOdd = !! (cpu_p->PPR.IC & 1);
    bool icEven = ! icOdd;

    // Here, repeat_first means that the instruction just executed was the
    // RPT or RPD; but when the even instruction of a RPD is executed,
    // repeat_first is still set, since repeat_first cannot be cleared
    // until the odd instruction gets its first execution. Put some
    // ugly logic in to detect that condition.

    bool rf = cpu_p->cu.repeat_first;
    if (rf && cpu_p->cu.rd && icEven)
      rf = false;

    if (unlikely ((! rf) && (cpu_p->cu.rpt || cpu_p->cu.rd || cpu_p->cu.rl)))
      {
        CPT (cpt2L, 7); // Post execution RPx
        // If we get here, the instruction just executed was a
        // RPT, RPD or RPL target instruction, and not the RPT or RPD
        // instruction itself

        if (cpu_p->cu.rpt || cpu_p->cu.rd)
          {
            // Add delta to index register.

            bool rptA = !! (cpu_p->rX[0] & 01000);
            bool rptB = !! (cpu_p->rX[0] & 00400);

            sim_debug (DBG_TRACEEXT, & cpu_dev,
                "RPT/RPD delta first %d rf %d rpt %d rd %d "
                "e/o %d X0 %06o a %d b %d\n",
                cpu_p->cu.repeat_first, rf, cpu_p->cu.rpt, cpu_p->cu.rd, icOdd,
                cpu_p->rX[0], rptA, rptB);

            if (cpu_p->cu.rpt) // rpt
              {
                CPT (cpt2L, 8); // RPT delta
                uint Xn = (uint) getbits36_3 (cpu_p->cu.IWB, 36 - 3);
                cpu_p->TPR.CA = (cpu_p->rX[Xn] + cpu_p->cu.delta) & AMASK;
                cpu_p->rX[Xn] = cpu_p->TPR.CA;
                HDBGRegX (Xn);
                sim_debug (DBG_TRACEEXT, & cpu_dev,
                           "RPT/RPD delta; X%d now %06o\n", Xn, cpu_p->rX[Xn]);
              }

            // a:RJ78/rpd6
            // We know that the X register is not to be incremented until
            // after both instructions have executed, so the following
            // if uses icOdd instead of the more sensical icEven.
            if (cpu_p->cu.rd && icOdd && rptA) // rpd, even instruction
              {
                CPT (cpt2L, 9); // RD even
                // a:RJ78/rpd7
                uint Xn = (uint) getbits36_3 (cpu_p->cu.IWB, 36 - 3);
                cpu_p->TPR.CA = (cpu_p->rX[Xn] + cpu_p->cu.delta) & AMASK;
                cpu_p->rX[Xn] = cpu_p->TPR.CA;
                HDBGRegX (Xn);
                sim_debug (DBG_TRACEEXT, & cpu_dev,
                           "RPT/RPD delta; X%d now %06o\n", Xn, cpu_p->rX[Xn]);
              }

            if (cpu_p->cu.rd && icOdd && rptB) // rpdb, odd instruction
              {
                CPT (cpt2L, 10); // RD odd
                // a:RJ78/rpd8
                uint Xn = (uint) getbits36_3 (cpu_p->cu.IRODD, 36 - 3);
                cpu_p->TPR.CA = (cpu_p->rX[Xn] + cpu_p->cu.delta) & AMASK;
                cpu_p->rX[Xn] = cpu_p->TPR.CA;
                HDBGRegX (Xn);
                sim_debug (DBG_TRACEEXT, & cpu_dev,
                           "RPT/RPD delta; X%d now %06o\n", Xn, cpu_p->rX[Xn]);
              }
          } // rpt || rd

#if 0
        else if (cpu_p->cu.rl)
          {
            CPT (cpt2L, 11); // RL
            // C(Xn) -> y
#if 1
            uint Xn = (uint) getbits36_3 (cpu_p->cu.IWB, 36 - 3);
            word18 lnk = GETHI36 (cpu_p->CY);
            cpu_p->CY &= MASK18;
            cpu_p->rX[Xn] = lnk;
            //putbits36 (& cpu_p->cu.IWB,  0, 18, lnk);
#else
            uint Xn = (uint) getbits36_3 (cpu_p->cu.IWB, 36 - 3);
            putbits36 (& cpu_p->cu.IWB,  0, 18, cpu_p->rX[Xn]);
#endif
          }
#endif

        // Check for termination conditions.

///////
//
// ISOLTS test 769 claims in test-02a that 'rpt;div' with a divide
// fault should delay the divide fault until after the tremination
// check (it checks that the tally should be decremented) and in test-02b 
// that 'rpl;div' with a divide fault should not due the termination
// check (the tally should not be decremented).
//
// This implies that rpt and rpl are handled differently; as a test
// trying:

#ifdef DPS8M
        if (cpu_p->cu.rl && cpu_p->dlyFlt)
#else // L68
        if ((cpu_p->cu.rl || cpu_p->cu.rpt || cpu_p->cu.rd) && cpu_p->dlyFlt)
#endif
          {
            CPT (cpt2L, 14); // Delayed fault
            doFault (cpu_p, cpu_p->dlyFltNum, cpu_p->dlySubFltNum, cpu_p->dlyCtx);
          }

// Sadly, it fixes ISOLTS 769 test 02a and 02b.
//
///////

        if (cpu_p->cu.rpt || (cpu_p->cu.rd && icOdd) || cpu_p->cu.rl)
          {
            CPT (cpt2L, 12); // RPx termination check
            bool exit = false;
            // The repetition cycle consists of the following steps:
            //  a. Execute the repeated instruction
            //  b. C(X0)0,7 - 1 -> C(X0)0,7
            // a:AL39/rpd9
            uint x = (uint) getbits18 (cpu_p->rX[0], 0, 8);
            x -= 1;
            x &= MASK8;
            putbits18 (& cpu_p->rX[0], 0, 8, x);
            HDBGRegX (0);

            //sim_debug (DBG_TRACEEXT, & cpu_dev, "x %03o rX[0] %06o\n", x, rX[0]);

            // a:AL39/rpd10
            //  c. If C(X0)0,7 = 0, then set the tally runout indicator ON
            //     and terminate

            sim_debug (DBG_TRACEEXT, & cpu_dev, "tally %d\n", x);
            if (x == 0)
              {
                sim_debug (DBG_TRACEEXT, & cpu_dev, "tally runout\n");
                SET_I_TALLY;
                exit = true;
              }
            else
              {
                sim_debug (DBG_TRACEEXT, & cpu_dev, "not tally runout\n");
                CLR_I_TALLY;
              }

            //  d. If a terminate condition has been met, then set
            //     the tally runout indicator OFF and terminate

            if (TST_I_ZERO && (cpu_p->rX[0] & 0100))
              {
                sim_debug (DBG_TRACEEXT, & cpu_dev, "is zero terminate\n");
                CLR_I_TALLY;
                exit = true;
              }
            if (!TST_I_ZERO && (cpu_p->rX[0] & 040))
              {
                sim_debug (DBG_TRACEEXT, & cpu_dev, "is not zero terminate\n");
                CLR_I_TALLY;
                exit = true;
              }
            if (TST_I_NEG && (cpu_p->rX[0] & 020))
              {
                sim_debug (DBG_TRACEEXT, & cpu_dev, "is neg terminate\n");
                CLR_I_TALLY;
                exit = true;
              }
            if (!TST_I_NEG && (cpu_p->rX[0] & 010))
              {
                sim_debug (DBG_TRACEEXT, & cpu_dev, "is not neg terminate\n");
                CLR_I_TALLY;
                exit = true;
              }
            if (TST_I_CARRY && (cpu_p->rX[0] & 04))
              {
                sim_debug (DBG_TRACEEXT, & cpu_dev, "is carry terminate\n");
                CLR_I_TALLY;
                exit = true;
              }
            if (!TST_I_CARRY && (cpu_p->rX[0] & 02))
              {
                sim_debug (DBG_TRACEEXT, & cpu_dev, "is not carry terminate\n");
                CLR_I_TALLY;
                exit = true;
              }
            if (TST_I_OFLOW && (cpu_p->rX[0] & 01))
              {
                sim_debug (DBG_TRACEEXT, & cpu_dev, "is overflow terminate\n");
// ISOLTS test ps805 says that on overflow the tally should be set.
                //CLR_I_TALLY;
                SET_I_TALLY;
                exit = true;
              }

            if (exit)
              {
                CPT (cpt2L, 13); // RPx terminated
                cpu_p->cu.rpt = false;
                cpu_p->cu.rd = false;
                cpu_p->cu.rl = false;
              }
            else
              {
                sim_debug (DBG_TRACEEXT, & cpu_dev, "not terminate\n");
              }
          } // if (cpu_p->cu.rpt || cpu_p->cu.rd & (cpu_p->PPR.IC & 1))

        if (cpu_p->cu.rl)
          {
            CPT (cpt2L, 11); // RL
            if (cpu_p->lnk == 0)
              {
                CPT (cpt2L, 13); // RPx terminated
                cpu_p->cu.rpt = false;
                cpu_p->cu.rd = false;
                cpu_p->cu.rl = false;
                SET_I_TALLY;
              }
            else
              {
                // C(Xn) -> y
#if 1
                uint Xn = (uint) getbits36_3 (cpu_p->cu.IWB, 36 - 3);
                //word18 lnk = GETHI36 (cpu_p->CY);
                //cpu_p->CY &= MASK18;
                cpu_p->rX[Xn] = cpu_p->lnk;
                HDBGRegX (Xn);
                //putbits36 (& cpu_p->cu.IWB,  0, 18, lnk);
#else
                uint Xn = (uint) getbits36_3 (cpu_p->cu.IWB, 36 - 3);
                putbits36 (& cpu_p->cu.IWB,  0, 18, cpu_p->rX[Xn]);
#endif
              }
          } // rl
      } // (! rf) && (cpu_p->cu.rpt || cpu_p->cu.rd)

    if (unlikely (cpu_p->dlyFlt))
      {
        CPT (cpt2L, 14); // Delayed fault
        doFault (cpu_p, cpu_p->dlyFltNum, cpu_p->dlySubFltNum, cpu_p->dlyCtx);
      }
///
/// executeInstruction: simh hooks
///

    cpu_p->instrCnt ++;

    if_sim_debug (DBG_REGDUMP, & cpu_dev)
    {
        char buf [256];
        sim_debug (DBG_REGDUMPAQI, &cpu_dev,
                   "A=%012"PRIo64" Q=%012"PRIo64" IR:%s\n",
                   cpu_p->rA, cpu_p->rQ, dump_flags (buf, cpu_p->cu.IR));

#ifndef __MINGW64__
        sim_debug (DBG_REGDUMPFLT, &cpu_dev,
                   "E=%03o A=%012"PRIo64" Q=%012"PRIo64" %.10Lg\n",
                   cpu_p->rE, cpu_p->rA, cpu_p->rQ, EAQToIEEElongdouble ());
#else
        sim_debug (DBG_REGDUMPFLT, &cpu_dev,
                   "E=%03o A=%012"PRIo64" Q=%012"PRIo64" %.10g\n",
                   cpu_p->rE, cpu_p->rA, cpu_p->rQ, EAQToIEEEdouble ());
#endif

        sim_debug (DBG_REGDUMPIDX, &cpu_dev,
                   "X[0]=%06o X[1]=%06o X[2]=%06o X[3]=%06o\n",
                   cpu_p->rX[0], cpu_p->rX[1], cpu_p->rX[2], cpu_p->rX[3]);
        sim_debug (DBG_REGDUMPIDX, &cpu_dev,
                   "X[4]=%06o X[5]=%06o X[6]=%06o X[7]=%06o\n",
                   cpu_p->rX[4], cpu_p->rX[5], cpu_p->rX[6], cpu_p->rX[7]);
        for (int n = 0 ; n < 8 ; n++)
        {
            sim_debug (DBG_REGDUMPPR, &cpu_dev,
                       "PR%d/%s: SNR=%05o RNR=%o WORDNO=%06o BITNO:%02o ARCHAR:%o ARBITNO:%02o\n",
                       n, PRalias[n], cpu_p->PR[n].SNR, cpu_p->PR[n].RNR, 
                       cpu_p->PR[n].WORDNO, GET_PR_BITNO (n),
                       GET_AR_CHAR (n), GET_AR_BITNO (n));
        }
        sim_debug (DBG_REGDUMPPPR, &cpu_dev,
                   "PRR:%o PSR:%05o P:%o IC:%06o\n",
                   cpu_p->PPR.PRR, cpu_p->PPR.PSR, cpu_p->PPR.P, cpu_p->PPR.IC);
        sim_debug (DBG_REGDUMPDSBR, &cpu_dev,
                   "ADDR:%08o BND:%05o U:%o STACK:%04o\n",
                   cpu_p->DSBR.ADDR, cpu_p->DSBR.BND, cpu_p->DSBR.U, cpu_p->DSBR.STACK);
    }

///
/// executeInstruction: done. (Whew!)
///

    return ret;
}

//static t_stat DoBasicInstruction (void);
//static t_stat DoEISInstruction (void);

static inline void overflow (cpu_state_t *cpu_p, bool ovf, bool dly, const char * msg)
  {
    CPT (cpt2L, 15); // overflow check
    // If an overflow occured and the repeat instruction is not inhibiting
    // overflow checking.
    if (ovf && chkOVF (cpu_p))
      {
        SET_I_OFLOW;
        // If overflows are not masked
        if (tstOVFfault (cpu_p))
          {
            CPT (cpt2L, 16); // overflow 
            // ISOLTS test ps768: Overflows set TRO.
            if (cpu_p->cu.rpt || cpu_p->cu.rd || cpu_p->cu.rl)
              {
                SET_I_TALLY;
              }
            if (dly)
              dlyDoFault (cpu_p, FAULT_OFL, fst_zero, msg);
            else
              doFault (cpu_p, FAULT_OFL, fst_zero, msg);
          }
      }
  }

// Return values
//  CONT_TRA
//  STOP_UNIMP
//  STOP_ILLOP
//  emCall()
//     STOP_HALT
//  scu_sscr()
//     STOP_BUG
//     STOP_WARN
//  scu_rmcm()
//     STOP_BUG
//  scu_smcm()
//  STOP_DIS
//  simh_hooks()
//    hard to document what this can return....
//  0
//

// CANFAULT
static t_stat doInstruction (cpu_state_t *cpu_p)
{
    DCDstruct * i = & cpu_p->currentInstruction;
    // AL39 says it is always cleared, but that makes no sense (what good
    // is an indicator bit if it is always 0 when you check it?). Clear it if
    // an multiword EIS is at bat.
    // NB: Never clearing it renders Multics unbootable.
    if (i->info->ndes > 0)
      CLR_I_MIF;

#ifdef L68
    cpu_p->ou.eac = 0;
    cpu_p->ou.RB1_FULL = 0;
    cpu_p->ou.RP_FULL = 0;
    cpu_p->ou.RS_FULL = 0;
    cpu_p->ou.STR_OP = 0;
    cpu_p->ou.cycle = 0;
#endif
    PNL (cpu_p->ou.RS = (word9) i->opcode);
    PNL (L68_ (DU_CYCLE_FDUD;)) // set DU idle
    cpu_p->skip_cu_hist = false;
    memcpy (& cpu_p->MR_cache, & cpu_p->MR, sizeof (cpu_p->MR_cache));

// This mapping keeps nonEIS/EIS ordering, making various tables cleaner
#define x0(n) (n)
#define x1(n) (n|01000)

    //t_stat ret =  i->opcodeX ? DoEISInstruction () : DoBasicInstruction ();
    uint32 opcode10 = i->opcode10;

#ifdef PANEL
    if (insGrp [opcode10])
      {
        word8 grp = insGrp [opcode10] - 1;
        uint row = grp / 36;
        uint col = grp % 36;
        CPT (cpt3U + row, col); // 3U 0-35, 3L 0-17
      }
    if (opcodes10[opcode10].reg_use & is_OU)
      {
        is_ou = true;
    // XXX Punt on RP FULL, RS FULL
        cpu_p->ou.RB1_FULL = cpu_p->ou.RP_FULL = cpu_p->ou.RS_FULL = 1;
        cpu_p->ou.cycle |= ou_GIN;
        cpu_p->ou.opsz = (opcodes10[i->opcode10].reg_use >> 12) & 037;
        word10 reguse = (opcodes10[i->opcode10].reg_use) & MASK10;
        cpu_p->ou.reguse = reguse;
        if (reguse & ru_A) CPT (cpt5U, 4);
        if (reguse & ru_Q) CPT (cpt5U, 5);
        if (reguse & ru_X0) CPT (cpt5U, 6);
        if (reguse & ru_X1) CPT (cpt5U, 7);
        if (reguse & ru_X2) CPT (cpt5U, 8);
        if (reguse & ru_X3) CPT (cpt5U, 9);
        if (reguse & ru_X4) CPT (cpt5U, 10);
        if (reguse & ru_X5) CPT (cpt5U, 11);
        if (reguse & ru_X6) CPT (cpt5U, 12);
        if (reguse & ru_X7) CPT (cpt5U, 13);
      }
#endif
#ifdef L68
    bool is_ou = false;
#endif

    switch (opcode10)
      {


// Operations sorted by frequency of use; should help with caching issues

// Operations counts from booting and build a boot tape from source:
//          1605873148: eppn
//           845109778: sprin
//           702257337: lda
//           637613648: tra
//           555520875: ldq
//           462569862: tze
//           322979813: tnz
//           288200618: stq
//           260400300: cmpq
//           192454329: anaq
//           187283749: sta
//           170691055: lprpn
//           167568868: eaxn
//           166842812: tsxn
//           161542573: stz
//           155129792: epbpn
//           153639462: cmpa
//           144804232: aos
//           133559646: cana
//           127230192: ldaq
//           119988496: tpnz
//           113295654: lxln
//           109645303: staq
//           109417021: tspn
//           108352453: als
//            96267840: rtcd
//            93570029: tmi
//            93161815: stxn
//            90485871: ldi
//            87421892: eraq
//            76632891: ora
//            75372023: adq
//            75036448: tmoz
//            64921645: spbpn
//            63595794: ana
//            62621406: fld
//            57281513: epaq
//            56066122: qls
//            55861962: sti
//            55186331: mlr
//            54388393: call6
//            50000721: lrl
//            49736026: sbq
//            49552594: tpl
//            46097756: cmpb
//            44484993: szn
//            41295856: arl
//            40019677: lrs
//            39386119: sprpn
//            36130580: ldxn
//            32168708: ersa
//            31817270: cmpxn
//            31280696: a9bd
//            29383886: era
//            29282465: lls
//            28714658: mpy
//            28508378: sba
//            24067324: anq
//            23963178: asq
//            23953122: nop
//            23643534: orsa
//            23083282: csl
//            20970795: sbxn
//            20109045: tct
//            18504719: stba
//            18297461: eaq
//            17130040: eaa
//            16035441: cmpc
//            15762874: sxln
//            15109836: lca
//            15013924: adxn
//            14159104: lcq
//            14049597: div
//            14043543: cmpaq
//            13528591: ada
//            12778888: ansa
//            12534711: trc
//            11710149: sbaq
//            11584853: neg
//            11456885: ttn
//            11356918: canq
//            10797383: rccl
//            10743245: asa
//            10100949: ttf
//             9691628: orq
//             9332512: adwp0-3
//             9251904: anxn
//             8076030: ldac
//             8061536: scd
//             7779639: adaq
//             7586713: xec
//             7506406: qrl
//             7442522: adl
//             6535658: stca
//             6359531: adlxn
//             6255134: sbla
//             5936484: stacq
//             5673345: eawp2
//             4671545: tnc
//             4230412: scm
//             4040255: sarn
//             4006015: oraq
//             3918690: adlq
//             3912600: stbq
//             3449053: lcxn
//             3368670: adla
//             3290057: qrs
//             3252438: ars
//             3143543: qlr
//             3098158: stac
//             2838451: mvne
//             2739787: lde
//             2680484: btd
//             2573170: erq
//             2279433: fno
//             2273692: smcm
//             2240713: ersq
//             2173455: sreg
//             2173196: lreg
//             2112784: mrl
//             2030237: mvt
//             2010819: stc2
//             2008675: fmp
//             1981148: llr
//             1915081: mvn
//             1846728: sblxn
//             1820604: fcmp
//             1765253: lcpr
//             1447485: stc1
//             1373184: ansxn
//             1337744: negl
//             1264062: rscr
//             1201563: adwp4-7
//             1198321: rmcm
//             1182814: sznc
//             1171307: sblq
//             1140227: spri
//             1139968: lpri
//             1133946: dvf
//             1059600: scpr
//              958321: stcq
//              837695: tctr
//              820615: s9bd
//              812523: rsw
//              769275: fad
//              729737: orsq
//              651623: scu
//              651612: rcu
//              606518: abd
//              603591: eawp1
//              555935: orsxn
//              525680: scmr
//              467605: spl
//              467405: lpl
//              463927: lra
//              416700: awd
//              384090: dtb
//              383544: cmk
//              382254: fst
//              378820: ssa
//              370308: sra
//              326432: alr
//              321319: ldt
//              319911: ldbr
//              319908: sbar
//              319907: lbar
//              310379: cams
//              303041: eawp7
//              299122: xed
//              294724: easp2
//              270712: sztl
//              252001: dfst
//              241844: ste
//              226970: absa
//              218891: cioc
//              184535: dfld
//              182347: camp
//              174567: ansq
//              169317: rpt
//              124972: erx2
//              121933: fneg
//              114697: cnaaq
//              111728: rpd
//              106892: dis
//               96801: tov
//               92283: fsb
//               86209: erx4
//               80564: eawp3
//               76911: canaq
//               65706: ufa
//               65700: dfcmp
//               64530: fdv
//               48215: ldqc
//               45994: dfad
//               37790: awca
//               27218: asxn
//               23203: eawp5
//               16947: gtb
//               11431: ersxn
//                9527: erx3
//                8888: ssdr
//                8888: ssdp
//                8888: sptr
//                8888: sptp
//                8170: ssq
//                7116: mp3d
//                6969: cmg
//                6878: dv3d
//                5615: eawp6
//                4859: easp1
//                4726: easp3
//                3157: ad2d
//                2807: eawp4
//                2807: easp4
//                2411: cwl
//                1912: teu
//                1912: teo
//                1798: cmpn
//                1625: easp6
//                 931: adlaq
//                 659: erx1
//                 500: ???
//                 388: csr
//                 215: sb3d
//                 176: dfdv
//                  93: stcd
//                  92: mp2d
//                  41: sscr
//                  26: dfmp
//                  14: ad3d
//                  12: mve
//                  11: dfsb
//                   5: sdbr
//                   4: trtf
//                   4: orxn
//                   3: sb2d
//                   2: scdr
//                   1: stt
//                   1: ret
//                   1: drl

        case x0 (0350):  // epp0
        case x1 (0351):  // epp1
        case x0 (0352):  // epp2
        case x1 (0353):  // epp3
        case x0 (0370):  // epp4
        case x1 (0371):  // epp5
        case x0 (0372):  // epp6
        case x1 (0373):  // epp7
          // For n = 0, 1, ..., or 7 as determined by operation code
          //   C(TPR.TRR) -> C(PRn.RNR)
          //   C(TPR.TSR) -> C(PRn.SNR)
          //   C(TPR.CA) -> C(PRn.WORDNO)
          //   C(TPR.TBR) -> C(PRn.BITNO)
          {
            // epp0 0350  101 000
            // epp1 1351  101 001
            // epp2 0352  101 010
            // epp3 1353  101 011
            // epp4 0370  111 000
            // epp5 1371  111 001
            // epp6 0372  111 010
            // epp7 1373  111 011
            //n = ((opcode10 & 020) ? 4 : 0) + (opcode10 & 03);
            uint n = ((opcode10 & 020) >> 2) | (opcode10 & 03);
            CPTUR (cptUsePRn + n);
            cpu_p->PR[n].RNR = cpu_p->TPR.TRR;
            cpu_p->PR[n].SNR = cpu_p->TPR.TSR;
            cpu_p->PR[n].WORDNO = cpu_p->TPR.CA;
            SET_PR_BITNO (n, cpu_p->TPR.TBR);
            HDBGRegPR (n);
          }
          break;

        case x0 (0250):  // spri0
        case x1 (0251):  // spri1
        case x0 (0252):  // spri2
        case x1 (0253):  // spri3
        case x0 (0650):  // spri4
        case x1 (0651):  // spri5
        case x0 (0652):  // spri6
        case x1 (0653):  // spri7

          // For n = 0, 1, ..., or 7 as determined by operation code
          //  000 -> C(Y-pair)0,2
          //  C(PRn.SNR) -> C(Y-pair)3,17
          //  C(PRn.RNR) -> C(Y-pair)18,20
          //  00...0 -> C(Y-pair)21,29
          //  (43)8 -> C(Y-pair)30,35
          //  C(PRn.WORDNO) -> C(Y-pair)36,53
          //  000 -> C(Y-pair)54,56
          //  C(PRn.BITNO) -> C(Y-pair)57,62
          //  00...0 -> C(Y-pair)63,71
          {
            // spri0 0250 0 010 101 000
            // spri1 1251 1 010 101 001
            // spri2 0252 0 010 101 010
            // spri3 1253 1 010 101 011
            // spri4 0650 0 110 101 000
            // spri5 1651 1 110 101 001
            // spri6 0652 0 110 101 010
            // spri7 1653 1 110 101 011
            //uint n = ((opcode10 & 0400) ? 4 : 0) + (opcode10 & 03);
            uint n = ((opcode10 & 0400) >> 6) | (opcode10 & 03);
            CPTUR (cptUsePRn + n);
            cpu_p->Ypair[0]  = 043;
            cpu_p->Ypair[0] |= ((word36) cpu_p->PR[n].SNR) << 18;
            cpu_p->Ypair[0] |= ((word36) cpu_p->PR[n].RNR) << 15;

            cpu_p->Ypair[1]  = (word36) cpu_p->PR[n].WORDNO << 18;
            cpu_p->Ypair[1] |= (word36) GET_PR_BITNO (n) << 9;
          }
          break;

        case x0 (0235):  // lda
          cpu_p->rA = cpu_p->CY;
          HDBGRegA ();
          SC_I_ZERO (cpu_p->rA == 0);
          SC_I_NEG (cpu_p->rA & SIGN36);
          break;

        case x0 (0710):  // tra
          // C(TPR.CA) -> C(PPR.IC)
          // C(TPR.TSR) -> C(PPR.PSR)
          do_caf (cpu_p);
          read_tra_op (cpu_p);
          return CONT_TRA;

        case x0 (0236):  // ldq
          cpu_p->rQ = cpu_p->CY;
          HDBGRegQ ();
          SC_I_ZERO (cpu_p->rQ == 0);
          SC_I_NEG (cpu_p->rQ & SIGN36);
          break;

        case x0 (0600):  // tze
          // If zero indicator ON then
          //   C(TPR.CA) -> C(PPR.IC)
          //   C(TPR.TSR) -> C(PPR.PSR)
          // otherwise, no change to C(PPR)
          if (TST_I_ZERO)
            {
              do_caf (cpu_p);
              read_tra_op (cpu_p);
              return CONT_TRA;
            }
          break;

        case x0 (0601):  // tnz
          // If zero indicator OFF then
          //     C(TPR.CA) -> C(PPR.IC)
          //     C(TPR.TSR) -> C(PPR.PSR)
          if (!TST_I_ZERO)
            {
              do_caf (cpu_p);
              read_tra_op (cpu_p);
              return CONT_TRA;
            }
          break;

        case x0 (0756): // stq
          cpu_p->CY = cpu_p->rQ;
          HDBGRegQ ();
          break;

        case x0 (0116):  // cmpq
          // C(Q) :: C(Y)
          cmp36 (cpu_p->rQ, cpu_p->CY, &cpu_p->cu.IR);
          break;

        case x0 (0377):  //< anaq
          // C(AQ)i & C(Y-pair)i -> C(AQ)i for i = (0, 1, ..., 71)
          {
              word72 tmp72 = YPAIRTO72 (cpu_p->Ypair);
              word72 trAQ = convert_to_word72 (cpu_p->rA, cpu_p->rQ);
#ifdef NEED_128
              trAQ = and_128 (trAQ, tmp72);
              trAQ = and_128 (trAQ, MASK72);

              SC_I_ZERO (iszero_128 (trAQ));
              SC_I_NEG (isnonzero_128 (and_128 (trAQ, SIGN72)));
#else
              trAQ = trAQ & tmp72;
              trAQ &= MASK72;

              SC_I_ZERO (trAQ == 0);
              SC_I_NEG (trAQ & SIGN72);
#endif
              convert_to_word36 (trAQ, &cpu_p->rA, &cpu_p->rQ);
              HDBGRegA ();
              HDBGRegQ ();
          }
          break;

        case x0 (0755):  // sta
          cpu_p->CY = cpu_p->rA;
          HDBGRegA ();
          break;

                         // lprpn
        case x0 (0760):  // lprp0
        case x0 (0761):  // lprp1
        case x0 (0762):  // lprp2
        case x0 (0763):  // lprp3
        case x0 (0764):  // lprp4
        case x0 (0765):  // lprp5
        case x0 (0766):  // lprp6
        case x0 (0767):  // lprp7
          // For n = 0, 1, ..., or 7 as determined by operation code
          //  C(TPR.TRR) -> C(PRn.RNR)
          //  If C(Y)0,1 != 11, then
          //    C(Y)0,5 -> C(PRn.BITNO);
          //  otherwise,
          //    generate command fault
          // If C(Y)6,17 = 11...1, then 111 -> C(PRn.SNR)0,2
          //  otherwise,
          // 000 -> C(PRn.SNR)0,2
          // C(Y)6,17 -> C(PRn.SNR)3,14
          // C(Y)18,35 -> C(PRn.WORDNO)
          {
              uint32 n = opcode10 & 07;  // get n
              CPTUR (cptUsePRn + n);
              cpu_p->PR[n].RNR = cpu_p->TPR.TRR;

// [CAC] sprpn says: If C(PRn.SNR) 0,2 are nonzero, and C(PRn.SNR) != 11...1,
// then a store fault (illegal pointer) will occur and C(Y) will not be changed.
// I interpret this has meaning that only the high bits should be set here

              if (((cpu_p->CY >> 34) & 3) != 3)
                {
                  word6 bitno = (cpu_p->CY >> 30) & 077;
                  SET_PR_BITNO (n, bitno);
                }
              else
                {
// fim.alm
// command_fault:
//           eax7      com       assume normal command fault
//           ldq       bp|mc.scu.port_stat_word check illegal action
//           canq      scu.ial_mask,dl
//           tnz       fixindex            nonzero, treat as normal case
//           ldq       bp|scu.even_inst_word check for LPRPxx instruction
//           anq       =o770400,dl
//           cmpq      lprp_insts,dl
//           tnz       fixindex            isn't LPRPxx, treat as normal

// ial_mask is checking SCU word 1, field IA: 0 means "no illegal action"

                    // Therefore the subfault well no illegal action, and
                    // Multics will peek it the instruction to deduce that it
                    // is a lprpn fault.
                  doFault (cpu_p, FAULT_CMD, fst_cmd_lprpn, "lprpn");
                }
// The SPRPn instruction stores only the low 12 bits of the 15 bit SNR.
// A special case is made for an SNR of all ones; it is stored as 12 1's.
// The pcode in AL39 handles this awkwardly; I believe this is
// the same, but in a more straightforward manner

             // Get the 12 bit operand SNR
             word12 oSNR = getbits36_12 (cpu_p->CY, 6);
             // Test for special case
             if (oSNR == 07777)
               cpu_p->PR[n].SNR = 077777;
             else
               cpu_p->PR[n].SNR = oSNR; // usigned word will 0-extend.
              //C(Y)18,35 -> C(PRn.WORDNO)
              cpu_p->PR[n].WORDNO = GETLO (cpu_p->CY);

              sim_debug (DBG_APPENDING, & cpu_dev,
                         "lprp%d CY 0%012"PRIo64", PR[n].RNR 0%o, "
                         "PR[n].BITNO 0%o, PR[n].SNR 0%o, PR[n].WORDNO %o\n",
                         n, cpu_p->CY, cpu_p->PR[n].RNR, GET_PR_BITNO (n),
                         cpu_p->PR[n].SNR, cpu_p->PR[n].WORDNO);
              HDBGRegPR (n);
          }
          break;

                         // eaxn
        case x0 (0620):  // eax0
        case x0 (0621):  // eax1
        case x0 (0622):  // eax2
        case x0 (0623):  // eax3
        case x0 (0624):  // eax4
        case x0 (0625):  // eax5
        case x0 (0626):  // eax6
        case x0 (0627):  // eax7
          {
            uint32 n = opcode10 & 07;  // get n
            cpu_p->rX[n] = cpu_p->TPR.CA;
            HDBGRegX (n);

            SC_I_ZERO (cpu_p->TPR.CA == 0);
            SC_I_NEG (cpu_p->TPR.CA & SIGN18);

          }
          break;

                         // tsxn
        case x0 (0700):  // tsx0
        case x0 (0701):  // tsx1
        case x0 (0702):  // tsx2
        case x0 (0703):  // tsx3
        case x0 (0704):  // tsx4
        case x0 (0705):  // tsx5
        case x0 (0706):  // tsx6
        case x0 (0707):  // tsx7
          // For n = 0, 1, ..., or 7 as determined by operation code
          //   C(PPR.IC) + 1 -> C(Xn)
          // C(TPR.CA) -> C(PPR.IC)
          // C(TPR.TSR) -> C(PPR.PSR)
          {
            // We can't set Xn yet as the CAF may refer to Xn
            word18 ret = (cpu_p->PPR.IC + 1) & MASK18;
            do_caf (cpu_p);
            read_tra_op (cpu_p);
            cpu_p->rX[opcode10 & 07] = ret;
            HDBGRegX (opcode10 & 07);
          }
          return CONT_TRA;

        case x0 (0450): // stz
          cpu_p->CY = 0;
          break;

                         // epbpn
        case x1 (0350):  // epbp0
        case x0 (0351):  // epbp1
        case x1 (0352):  // epbp2
        case x0 (0353):  // epbp3
        case x1 (0370):  // epbp4
        case x0 (0371):  // epbp5
        case x1 (0372):  // epbp6
        case x0 (0373):  // epbp7
          // For n = 0, 1, ..., or 7 as determined by operation code
          //  C(TPR.TRR) -> C(PRn.RNR)
          //  C(TPR.TSR) -> C(PRn.SNR)
          //  00...0 -> C(PRn.WORDNO)
          //  0000 -> C(PRn.BITNO)
          {
            // epbp0 1350 101 000
            // epbp1 0351 101 000
            // epbp2 1352 101 000
            // epbp3 0353 101 000
            // epbp4 1370 111 000
            // epbp4 0371 111 000
            // epbp6 1372 111 000
            // epbp7 0373 111 000
            //n = ((opcode10 & 020) ? 4 : 0) + (opcode10 & 03);
            uint n = ((opcode10 & 020) >> 2) | (opcode10 & 03);
            CPTUR (cptUsePRn + n);
            cpu_p->PR[n].RNR = cpu_p->TPR.TRR;
            cpu_p->PR[n].SNR = cpu_p->TPR.TSR;
            cpu_p->PR[n].WORDNO = 0;
            SET_PR_BITNO (n, 0);
            HDBGRegPR (n);
          }
          break;

        case x0 (0115):  // cmpa
          // C(A) :: C(Y)
          cmp36 (cpu_p->rA, cpu_p->CY, &cpu_p->cu.IR);
          break;

        case x0 (0054):   // aos
          {
            // C(Y)+1->C(Y)

#ifdef L68
            cpu_p->ou.cycle |= ou_GOS;
#endif
            bool ovf;
            cpu_p->CY = Add36b (cpu_p->CY, 1, 0, I_ZNOC,
                                 & cpu_p->cu.IR, & ovf);
            overflow (cpu_p, ovf, true, "aos overflow fault");
#ifdef TEST_OLIN
          cmpxchg ();
#endif
          }
          break;


        case x0 (0315):  // cana
          // C(Z)i = C(A)i & C(Y)i for i = (0, 1, ..., 35)
          {
            word36 trZ = cpu_p->rA & cpu_p->CY;
            trZ &= MASK36;

            SC_I_ZERO (trZ == 0);
            SC_I_NEG (trZ & SIGN36);
          }
          break;

        case x0 (0237):  // ldaq
          cpu_p->rA = cpu_p->Ypair[0];
          HDBGRegA ();
          cpu_p->rQ = cpu_p->Ypair[1];
          HDBGRegQ ();
          SC_I_ZERO (cpu_p->rA == 0 && cpu_p->rQ == 0)
          SC_I_NEG (cpu_p->rA & SIGN36);
          break;

        case x1 (0605):  // tpnz
            // If negative and zero indicators are OFF then
            //  C(TPR.CA) -> C(PPR.IC)
            //  C(TPR.TSR) -> C(PPR.PSR)
            if (! (cpu_p->cu.IR & I_NEG) && ! (cpu_p->cu.IR & I_ZERO))
            {
                do_caf (cpu_p);
                read_tra_op (cpu_p);
                return CONT_TRA;
            }
            break;

                         // lxln
        case x0 (0720):  // lxl0
        case x0 (0721):  // lxl1
        case x0 (0722):  // lxl2
        case x0 (0723):  // lxl3
        case x0 (0724):  // lxl4
        case x0 (0725):  // lxl5
        case x0 (0726):  // lxl6
        case x0 (0727):  // lxl7
          {
            uint32 n = opcode10 & 07;  // get n
            cpu_p->rX[n] = GETLO (cpu_p->CY);
            HDBGRegX (n);
            SC_I_ZERO (cpu_p->rX[n] == 0);
            SC_I_NEG (cpu_p->rX[n] & SIGN18);
          }
          break;

        case x0 (0757):  // staq
          cpu_p->Ypair[0] = cpu_p->rA;
          cpu_p->Ypair[1] = cpu_p->rQ;
          break;

                         // tspn
        case x0 (0270):  // tsp0
        case x0 (0271):  // tsp1
        case x0 (0272):  // tsp2
        case x0 (0273):  // tsp3
        case x0 (0670):  // tsp4
        case x0 (0671):  // tsp5
        case x0 (0672):  // tsp6
        case x0 (0673):  // tsp7
          // For n = 0, 1, ..., or 7 as determined by operation code
          //  C(PPR.PRR) -> C(PRn.RNR)
          //  C(PPR.PSR) -> C(PRn.SNR)
          //  C(PPR.IC) + 1 -> C(PRn.WORDNO)
          //  00...0 -> C(PRn.BITNO)
          //  C(TPR.CA) -> C(PPR.IC)
          //  C(TPR.TSR) -> C(PPR.PSR)
          {
            uint32 n;
            if (opcode10 <= 0273)
              n = (opcode10 & 3);
            else
              n = (opcode10 & 3) + 4;
            CPTUR (cptUsePRn + n);

            do_caf (cpu_p);
            // PR[n] is set in read_tra_op().
            read_tra_op (cpu_p);
          }
          return CONT_TRA;

        case x0 (0735):  // als
          {
            word36 tmp36 = cpu_p->TPR.CA & 0177;   // CY bits 11-17

            word36 tmpSign = cpu_p->rA & SIGN36;
            CLR_I_CARRY;

            for (uint j = 0; j < tmp36; j ++)
              {
                cpu_p->rA <<= 1;
                if (tmpSign != (cpu_p->rA & SIGN36))
                  SET_I_CARRY;
              }
            cpu_p->rA &= DMASK;    // keep to 36-bits
            HDBGRegA ();

            SC_I_ZERO (cpu_p->rA == 0);
            SC_I_NEG (cpu_p->rA & SIGN36);
          }
          break;

        case x0 (0610):  // rtcd
          // If an access violation fault occurs when fetching the SDW for
          // the Y-pair, the C(PPR.PSR) and C(PPR.PRR) are not altered.

          do_caf (cpu_p);
          Read2 (cpu_p, cpu_p->TPR.CA, cpu_p->Ypair, RTCD_OPERAND_FETCH);
          // RTCD always ends up in append mode.
          set_addr_mode (cpu_p, APPEND_mode);
            
          return CONT_TRA;

        case x0 (0604):  // tmi
          // If negative indicator ON then
          //  C(TPR.CA) -> C(PPR.IC)
          //  C(TPR.TSR) -> C(PPR.PSR)
          if (TST_I_NEG)
            {
              do_caf (cpu_p);
              read_tra_op (cpu_p);
              return CONT_TRA;
            }
          break;

                         // stxn
        case x0 (0740):  // stx0
        case x0 (0741):  // stx1
        case x0 (0742):  // stx2
        case x0 (0743):  // stx3
        case x0 (0744):  // stx4
        case x0 (0745):  // stx5
        case x0 (0746):  // stx6
        case x0 (0747):  // stx7
          {
            uint32 n = opcode10 & 07;  // get n
            //SETHI (cpu_p->CY, cpu_p->rX[n]);
            cpu_p->CY = ((word36) cpu_p->rX[n]) << 18;
            cpu_p->zone = 0777777000000;
            cpu_p->useZone = true;
          }
#ifdef TEST_OLIN
          cmpxchg ();
#endif
          break;

        case x0 (0634):  // ldi
          {
            CPTUR (cptUseIR);
            // C(Y)18,31 -> C(IR)

            // Indicators:
            //  Parity Mask:
            //      If C(Y)27 = 1, and the processor is in absolute or
            //      instruction privileged mode, then ON; otherwise OFF.
            //      This indicator is not affected in the normal or BAR modes.
            //  Not BAR mode:
            //      Cannot be changed by the ldi instruction
            //  MIF:
            //      If C(Y)30 = 1, and the processor is in absolute or
            //      instruction privileged mode, then ON; otherwise OFF.
            //      This indicator is not affected in normal or BAR modes.
            //  Absolute mode:
            //      Cannot be changed by the ldi instruction
            //  All others: If corresponding bit in C(Y) is 1, then ON;
            //  otherwise, OFF

            // upper 14-bits of lower 18-bits

            // AL39 ldi says that HEX is ignored, but the mode register 
            // description says that it isn't
#ifdef DPS8M
            word18 tmp18 = GETLO (cpu_p->CY) & 0777770;
#endif
#ifdef L68
            word18 tmp18 = GETLO (cpu_p->CY) & 0777760;
#endif

            bool bAbsPriv = is_priv_mode (cpu_p);

            SC_I_ZERO  (tmp18 & I_ZERO);
            SC_I_NEG   (tmp18 & I_NEG);
            SC_I_CARRY (tmp18 & I_CARRY);
            SC_I_OFLOW (tmp18 & I_OFLOW);
            SC_I_EOFL  (tmp18 & I_EOFL);
            SC_I_EUFL  (tmp18 & I_EUFL);
            SC_I_OMASK (tmp18 & I_OMASK);
            SC_I_TALLY (tmp18 & I_TALLY);
            SC_I_PERR  (tmp18 & I_PERR);
            // I_PMASK handled below
            // LDI cannot change I_NBAR
            SC_I_TRUNC (tmp18 & I_TRUNC);
            // I_MIF handled below
            // LDI cannot change I_ABS
#ifdef DPS8M
            SC_I_HEX  (tmp18 & I_HEX);
#endif

#if 0
            cpu_p->bar_attempt = false;

#endif
            if (bAbsPriv)
              {
                SC_I_PMASK (tmp18 & I_PMASK);
                SC_I_MIF (tmp18 & I_MIF);
#if 0
                if (! (tmp18 & I_NBAR))
                  {
                    cpu_p->bar_attempt = true;
                  }
#endif
              }
            else
              {
                CLR_I_PMASK;
                CLR_I_MIF;
              }
          }
          break;

        case x0 (0677):  // eraq
          // C(AQ)i XOR C(Y-pair)i -> C(AQ)i for i = (0, 1, ..., 71)
          {
            word72 tmp72 = YPAIRTO72 (cpu_p->Ypair);
            word72 trAQ = convert_to_word72 (cpu_p->rA, cpu_p->rQ);
#ifdef NEED_128
            trAQ = xor_128 (trAQ, tmp72);
            trAQ = and_128 (trAQ, MASK72);

            SC_I_ZERO (iszero_128 (trAQ));
            SC_I_NEG (isnonzero_128 (and_128 (trAQ, SIGN72)));
#else
            trAQ = trAQ ^ tmp72;
            trAQ &= MASK72;

            SC_I_ZERO (trAQ == 0);
            SC_I_NEG (trAQ & SIGN72);
#endif

            convert_to_word36 (trAQ, &cpu_p->rA, &cpu_p->rQ);
            HDBGRegA ();
            HDBGRegQ ();
          }
          break;

        case x0 (0275):  // ora
          // C(A)i | C(Y)i -> C(A)i for i = (0, 1, ..., 35)
          cpu_p->rA = cpu_p->rA | cpu_p->CY;
          cpu_p->rA &= DMASK;
          HDBGRegA ();

          SC_I_ZERO (cpu_p->rA == 0);
          SC_I_NEG (cpu_p->rA & SIGN36);
          break;

        case x0 (0076):   // adq
          {
#ifdef L68
            cpu_p->ou.cycle |= ou_GOS;
#endif
            bool ovf;
            cpu_p->rQ = Add36b (cpu_p->rQ, cpu_p->CY, 0, I_ZNOC,
                                 & cpu_p->cu.IR, & ovf);
            HDBGRegQ ();
            overflow (cpu_p, ovf, false, "adq overflow fault");
          }
          break;

        case x1 (0604):  // tmoz
            // If negative or zero indicator ON then
            // C(TPR.CA) -> C(PPR.IC)
            // C(TPR.TSR) -> C(PPR.PSR)
            if (cpu_p->cu.IR & (I_NEG | I_ZERO))
              {
                do_caf (cpu_p);
                read_tra_op (cpu_p);
                return CONT_TRA;
              }
            break;


        case x1 (0250):  // spbp0
        case x0 (0251):  // spbp1
        case x1 (0252):  // spbp2
        case x0 (0253):  // spbp3
        case x1 (0650):  // spbp4
        case x0 (0651):  // spbp5
        case x1 (0652):  // spbp6
        case x0 (0653):  // spbp7
            // For n = 0, 1, ..., or 7 as determined by operation code
            //  C(PRn.SNR) -> C(Y-pair)3,17
            //  C(PRn.RNR) -> C(Y-pair)18,20
            //  000 -> C(Y-pair)0,2
            //  00...0 -> C(Y-pair)21,29
            //  (43)8 -> C(Y-pair)30,35
            //  00...0 -> C(Y-pair)36,71
            {
              // spbp0 1250  010 101 000
              // spbp1 0251  010 101 001
              // spbp2 1252  010 101 010
              // spbp3 0253  010 101 011
              // spbp4 1650  110 101 000
              // spbp5 0651  110 101 001
              // spbp6 1652  110 101 010
              // spbp8 0653  110 101 011
              uint n = ((opcode10 & 0400) >> 6) | (opcode10 & 03);
              CPTUR (cptUsePRn + n);
              cpu_p->Ypair[0] = 043;
              cpu_p->Ypair[0] |= ((word36) cpu_p->PR[n].SNR) << 18;
              cpu_p->Ypair[0] |= ((word36) cpu_p->PR[n].RNR) << 15;
              cpu_p->Ypair[1] = 0;
            }
            break;

        case x0 (0375):  // ana
          // C(A)i & C(Y)i -> C(A)i for i = (0, 1, ..., 35)
          cpu_p->rA = cpu_p->rA & cpu_p->CY;
          cpu_p->rA &= DMASK;
          HDBGRegA ();
          SC_I_ZERO (cpu_p->rA == 0);
          SC_I_NEG (cpu_p->rA & SIGN36);
          break;

        case x0 (0431):  // fld
          // C(Y)0,7 -> C(E)
          // C(Y)8,35 -> C(AQ)0,27
          // 00...0 -> C(AQ)30,71
          // Zero: If C(AQ) = 0, then ON; otherwise OFF
          // Neg: If C(AQ)0 = 1, then ON; otherwise OFF

          CPTUR (cptUseE);
          cpu_p->CY &= DMASK;
          cpu_p->rE = (cpu_p->CY >> 28) & 0377;
          cpu_p->rA = (cpu_p->CY & FLOAT36MASK) << 8;
          HDBGRegA ();
          cpu_p->rQ = 0;
          HDBGRegQ ();

          SC_I_ZERO (cpu_p->rA == 0 && cpu_p->rQ == 0);
          SC_I_NEG (cpu_p->rA & SIGN36);
          break;

        case x0 (0213):  // epaq
          // 000 -> C(AQ)0,2
          // C(TPR.TSR) -> C(AQ)3,17
          // 00...0 -> C(AQ)18,32
          // C(TPR.TRR) -> C(AQ)33,35

          // C(TPR.CA) -> C(AQ)36,53
          // 00...0 -> C(AQ)54,65
          // C(TPR.TBR) -> C(AQ)66,71

          cpu_p->rA = cpu_p->TPR.TRR & MASK3;
          cpu_p->rA |= (word36) (cpu_p->TPR.TSR & MASK15) << 18;
          HDBGRegA ();

          cpu_p->rQ = cpu_p->TPR.TBR & MASK6;
          cpu_p->rQ |= (word36) (cpu_p->TPR.CA & MASK18) << 18;
          HDBGRegQ ();

          SC_I_ZERO (cpu_p->rA == 0 && cpu_p->rQ == 0);

          break;

        case x0 (0736):  // qls
          // Shift C(Q) left the number of positions given in
          // C(TPR.CA)11,17; fill vacated positions with zeros.
          {
            word36 tmp36 = cpu_p->TPR.CA & 0177;   // CY bits 11-17
            word36 tmpSign = cpu_p->rQ & SIGN36;
            CLR_I_CARRY;

            for (uint j = 0; j < tmp36; j ++)
              {
                cpu_p->rQ <<= 1;
                if (tmpSign != (cpu_p->rQ & SIGN36))
                  SET_I_CARRY;
              }
            cpu_p->rQ &= DMASK;    // keep to 36-bits
            HDBGRegQ ();

            SC_I_ZERO (cpu_p->rQ == 0);
            SC_I_NEG (cpu_p->rQ & SIGN36);
          }
          break;

        case x0 (0754): // sti

          // C(IR) -> C(Y)18,31
          // 00...0 -> C(Y)32,35

          // The contents of the indicator register after address
          // preparation are stored in C(Y)18,31  C(Y)18,31 reflects the
          // state of the tally runout indicator prior to address
          // preparation. The relation between C(Y)18,31 and the indicators
          // is given in Table 4-5.

          CPTUR (cptUseIR);
            // AL39 sti says that HEX is ignored, but the mode register 
            // description says that it isn't
#ifdef DPS8M
          //SETLO (cpu_p->CY, (cpu_p->cu.IR & 0000000777770LL));
          cpu_p->CY = cpu_p->cu.IR & 0000000777770LL;
#endif
#ifdef L68
          //SETLO (cpu_p->CY, (cpu_p->cu.IR & 0000000777760LL));
          cpu_p->CY = cpu_p->cu.IR & 0000000777760LL;
#endif
          cpu_p->zone = 0000000777777;
          cpu_p->useZone = true;
          SCF (i->stiTally, cpu_p->CY, I_TALLY);
#ifdef TEST_OLIN
          cmpxchg ();
#endif
          break;


        ///    FIXED-POINT ARITHMETIC INSTRUCTIONS

        /// Fixed-Point Data Movement Load

        case x0 (0635):  // eaa
          cpu_p->rA = 0;
          SETHI (cpu_p->rA, cpu_p->TPR.CA);
          HDBGRegA ();
          SC_I_ZERO (cpu_p->TPR.CA == 0);
          SC_I_NEG (cpu_p->TPR.CA & SIGN18);

          break;

        case x0 (0636):  // eaq
          cpu_p->rQ = 0;
          SETHI (cpu_p->rQ, cpu_p->TPR.CA);
          HDBGRegQ ();

          SC_I_ZERO (cpu_p->TPR.CA == 0);
          SC_I_NEG (cpu_p->TPR.CA & SIGN18);

          break;

// Optimized to the top of the loop
//        case x0 (0620):  // eax0
//        case x0 (0621):  // eax1
//        case x0 (0622):  // eax2
//        case x0 (0623):  // eax3
//        case x0 (0624):  // eax4
//        case x0 (0625):  // eax5
//        case x0 (0626):  // eax6
//        case x0 (0627):  // eax7

        case x0 (0335):  // lca
          {
            bool ovf;
            cpu_p->rA = compl36 (cpu_p->CY, & cpu_p->cu.IR, & ovf);
            HDBGRegA ();
            overflow (cpu_p, ovf, false, "lca overflow fault");
          }
          break;

        case x0 (0336):  // lcq
          {
            bool ovf;
            cpu_p->rQ = compl36 (cpu_p->CY, & cpu_p->cu.IR, & ovf);
            HDBGRegQ ();
            overflow (cpu_p, ovf, false, "lcq overflow fault");
          }
          break;

                         // lcxn
        case x0 (0320):  // lcx0
        case x0 (0321):  // lcx1
        case x0 (0322):  // lcx2
        case x0 (0323):  // lcx3
        case x0 (0324):  // lcx4
        case x0 (0325):  // lcx5
        case x0 (0326):  // lcx6
        case x0 (0327):  // lcx7
          {
            bool ovf;
            uint32 n = opcode10 & 07;  // get n
            cpu_p->rX[n] = compl18 (GETHI (cpu_p->CY), & cpu_p->cu.IR, & ovf);
            HDBGRegX (n);
            overflow (cpu_p, ovf, false, "lcxn overflow fault");
          }
          break;

        case x0 (0337):  // lcaq
          {
            // The lcaq instruction changes the number to its negative while
            // moving it from Y-pair to AQ. The operation is executed by
            // forming the twos complement of the string of 72 bits. In twos
            // complement arithmetic, the value 0 is its own negative. An
            // overflow condition exists if C(Y-pair) = -2**71.


            if (cpu_p->Ypair[0] == 0400000000000LL && cpu_p->Ypair[1] == 0)
              {
                cpu_p->rA = cpu_p->Ypair[0];
                HDBGRegA ();
                cpu_p->rQ = cpu_p->Ypair[1];
                HDBGRegQ ();
                SET_I_NEG;
                CLR_I_ZERO;
                overflow (cpu_p, true, false, "lcaq overflow fault");
              }
            else if (cpu_p->Ypair[0] == 0 && cpu_p->Ypair[1] == 0)
              {
                cpu_p->rA = 0;
                HDBGRegA ();
                cpu_p->rQ = 0;
                HDBGRegQ ();

                SET_I_ZERO;
                CLR_I_NEG;
              }
            else
              {
                word72 tmp72 = convert_to_word72 (cpu_p->Ypair[0], cpu_p->Ypair[1]);
#ifdef NEED_128
                tmp72 = negate_128 (tmp72);
#else
                tmp72 = ~tmp72 + 1;
#endif
                convert_to_word36 (tmp72, & cpu_p->rA, & cpu_p->rQ);
                HDBGRegA ();
                HDBGRegQ ();

                SC_I_ZERO (cpu_p->rA == 0 && cpu_p->rQ == 0);
                SC_I_NEG (cpu_p->rA & SIGN36);
              }
          }
          break;

// Optimized to the top of the loop
//        case x0 (0235):  // lda

        case x0 (0034): // ldac
          cpu_p->rA = cpu_p->CY;
          HDBGRegA ();
          SC_I_ZERO (cpu_p->rA == 0);
          SC_I_NEG (cpu_p->rA & SIGN36);
          cpu_p->CY = 0;
#ifdef TEST_OLIN
          cmpxchg ();
#endif
          break;

// Optimized to the top of the loop
//        case x0 (0237):  // ldaq

// Optimized to the top of the loop
//        case x0 (0634):  // ldi

// Optimized to the top of the loop
//         case x0 (0236):  // ldq

        case x0 (0032): // ldqc
          cpu_p->rQ = cpu_p->CY;
          HDBGRegQ ();
          SC_I_ZERO (cpu_p->rQ == 0);
          SC_I_NEG (cpu_p->rQ & SIGN36);
          cpu_p->CY = 0;
#ifdef TEST_OLIN
          cmpxchg ();
#endif
          break;

                         // ldxn
        case x0 (0220):  // ldx0
        case x0 (0221):  // ldx1
        case x0 (0222):  // ldx2
        case x0 (0223):  // ldx3
        case x0 (0224):  // ldx4
        case x0 (0225):  // ldx5
        case x0 (0226):  // ldx6
        case x0 (0227):  // ldx7
          {
            uint32 n = opcode10 & 07;  // get n
            cpu_p->rX[n] = GETHI (cpu_p->CY);
            HDBGRegX (n);
            SC_I_ZERO (cpu_p->rX[n] == 0);
            SC_I_NEG (cpu_p->rX[n] & SIGN18);
          }
          break;

        case x0 (0073):   // lreg
          CPTUR (cptUseE);
#ifdef L68
          cpu_p->ou.cycle |= ou_GOS;
          cpu_p->ou.eac = 0;
#endif
          cpu_p->rX[0] = GETHI (cpu_p->Yblock8[0]);
          HDBGRegX (0);
          cpu_p->rX[1] = GETLO (cpu_p->Yblock8[0]);
          HDBGRegX (1);
#ifdef L68
          cpu_p->ou.eac ++;
#endif
          cpu_p->rX[2] = GETHI (cpu_p->Yblock8[1]);
          HDBGRegX (2);
          cpu_p->rX[3] = GETLO (cpu_p->Yblock8[1]);
          HDBGRegX (3);
#ifdef L68
          cpu_p->ou.eac ++;
#endif
          cpu_p->rX[4] = GETHI (cpu_p->Yblock8[2]);
          HDBGRegX (4);
          cpu_p->rX[5] = GETLO (cpu_p->Yblock8[2]);
          HDBGRegX (5);
#ifdef L68
          cpu_p->ou.eac ++;
#endif
          cpu_p->rX[6] = GETHI (cpu_p->Yblock8[3]);
          HDBGRegX (6);
          cpu_p->rX[7] = GETLO (cpu_p->Yblock8[3]);
          HDBGRegX (7);
#ifdef L68
          cpu_p->ou.eac = 0;
#endif
          cpu_p->rA = cpu_p->Yblock8[4];
          HDBGRegA ();
          cpu_p->rQ = cpu_p->Yblock8[5];
          HDBGRegQ ();
          cpu_p->rE = (GETHI (cpu_p->Yblock8[6]) >> 10) & 0377;   // need checking
          break;

// Optimized to the top of the loop
//                         // lxln
//        case x0 (0720):  // lxl0
//        case x0 (0721):  // lxl1
//        case x0 (0722):  // lxl2
//        case x0 (0723):  // lxl3
//        case x0 (0724):  // lxl4
//        case x0 (0725):  // lxl5
//        case x0 (0726):  // lxl6
//        case x0 (0727):  // lxl7

        /// Fixed-Point Data Movement Store

        case x0 (0753):  // sreg
          CPTUR (cptUseE);
          CPTUR (cptUseRALR);
          // clear block (changed to memset() per DJ request)
          //memset (cpu_p->Yblock8, 0, sizeof (cpu_p->Yblock8));
#ifdef L68
          cpu_p->ou.cycle |= ou_GOS;
          cpu_p->ou.eac = 0;
#endif
          SETHI (cpu_p->Yblock8[0], cpu_p->rX[0]);
          SETLO (cpu_p->Yblock8[0], cpu_p->rX[1]);
#ifdef L68
          cpu_p->ou.eac ++;
#endif
          SETHI (cpu_p->Yblock8[1], cpu_p->rX[2]);
          SETLO (cpu_p->Yblock8[1], cpu_p->rX[3]);
#ifdef L68
          cpu_p->ou.eac ++;
#endif
          SETHI (cpu_p->Yblock8[2], cpu_p->rX[4]);
          SETLO (cpu_p->Yblock8[2], cpu_p->rX[5]);
#ifdef L68
          cpu_p->ou.eac ++;
#endif
          SETHI (cpu_p->Yblock8[3], cpu_p->rX[6]);
          SETLO (cpu_p->Yblock8[3], cpu_p->rX[7]);
#ifdef L68
          cpu_p->ou.eac = 0;
#endif
          cpu_p->Yblock8[4] = cpu_p->rA;
          HDBGRegA ();
          cpu_p->Yblock8[5] = cpu_p->rQ;
          HDBGRegQ ();
          cpu_p->Yblock8[6] = ((word36)(cpu_p->rE & MASK8)) << 28;
#ifdef ISOLTS
          if (current_running_cpu_idx)
            cpu_p->Yblock8[7] = (((-- cpu_p->shadowTR) & MASK27) << 9) | (cpu_p->rRALR & 07);
          else
            cpu_p->Yblock8[7] = ((cpu_p->rTR & MASK27) << 9) | (cpu_p->rRALR & 07);

#else
          cpu_p->Yblock8[7] = ((cpu_p->rTR & MASK27) << 9) | (cpu_p->rRALR & 07);
#endif
          break;

// Optimized to the top of the loop
//        case x0 (0755):  // sta

        case x0 (0354):  // stac
          if (cpu_p->CY == 0)
            {
              SET_I_ZERO;
              cpu_p->CY = cpu_p->rA;
            }
          else
            CLR_I_ZERO;
#ifdef TEST_OLIN
          cmpxchg ();
#endif
          break;

        case x0 (0654):  // stacq
          if (cpu_p->CY == cpu_p->rQ)
            {
              cpu_p->CY = cpu_p->rA;
              SET_I_ZERO;
            }
          else
            CLR_I_ZERO;
#ifdef TEST_OLIN
          cmpxchg ();
#endif
          break;

// Optimized to the top of the loop
//        case x0 (0757):  // staq

        case x0 (0551):  // stba
          // 9-bit bytes of C(A) -> corresponding bytes of C(Y), the byte
          // positions affected being specified in the TAG field.
          //copyBytes ((i->tag >> 2) & 0xf, cpu_p->rA, &cpu_p->CY);
          cpu_p->CY = cpu_p->rA;
          cpu_p->zone =
             ((i->tag & 040) ? 0777000000000u : 0) |
             ((i->tag & 020) ? 0000777000000u : 0) |
             ((i->tag & 010) ? 0000000777000u : 0) |
             ((i->tag & 004) ? 0000000000777u : 0);
          cpu_p->useZone = true;
          cpu_p->ou.crflag = true;
#ifdef TEST_OLIN
          cmpxchg ();
#endif
          break;

        case x0 (0552):  // stbq
          // 9-bit bytes of C(Q) -> corresponding bytes of C(Y), the byte
          // positions affected being specified in the TAG field.
          //copyBytes ((i->tag >> 2) & 0xf, cpu_p->rQ, &cpu_p->CY);
          cpu_p->CY = cpu_p->rQ;
          cpu_p->zone =
             ((i->tag & 040) ? 0777000000000u : 0) |
             ((i->tag & 020) ? 0000777000000u : 0) |
             ((i->tag & 010) ? 0000000777000u : 0) |
             ((i->tag & 004) ? 0000000000777u : 0);
          cpu_p->useZone = true;
          cpu_p->ou.crflag = true;
#ifdef TEST_OLIN
          cmpxchg ();
#endif
          break;

        case x0 (0554):  // stc1
          // "C(Y)25 reflects the state of the tally runout indicator
          // prior to modification.
          SETHI (cpu_p->CY, (cpu_p->PPR.IC + 1) & MASK18);
          // AL39 stc1 says that HEX is ignored, but the mode register 
          // description says that it isn't
#ifdef DPS8M
          SETLO (cpu_p->CY, cpu_p->cu.IR & 0777770);
#endif
#ifdef L68
          SETLO (cpu_p->CY, cpu_p->cu.IR & 0777760);
#endif
          SCF (i->stiTally, cpu_p->CY, I_TALLY);
          break;

        case x0 (0750):  // stc2
          // AL-39 doesn't specify if the low half is set to zero,
          // set to IR, or left unchanged
          // RJ78 specifies unchanged
          //SETHI (cpu_p->CY, (cpu_p->PPR.IC + 2) & MASK18);
          cpu_p->CY = ((word36) ((cpu_p->PPR.IC + 2) & MASK18)) << 18;
          cpu_p->zone = 0777777000000;
          cpu_p->useZone = true;
#ifdef TEST_OLIN
          cmpxchg ();
#endif
          break;

        case x0 (0751): // stca
          // Characters of C(A) -> corresponding characters of C(Y),
          // the character positions affected being specified in the TAG
          // field.
          //copyChars (i->tag, cpu_p->rA, &cpu_p->CY);
          cpu_p->CY = cpu_p->rA;
          cpu_p->zone =
             ((i->tag & 040) ? 0770000000000u : 0) |
             ((i->tag & 020) ? 0007700000000u : 0) |
             ((i->tag & 010) ? 0000077000000u : 0) |
             ((i->tag & 004) ? 0000000770000u : 0) |
             ((i->tag & 002) ? 0000000007700u : 0) |
             ((i->tag & 001) ? 0000000000077u : 0);
          cpu_p->useZone = true;
          cpu_p->ou.crflag = true;
#ifdef TEST_OLIN
          cmpxchg ();
#endif
          break;

        case x0 (0752): // stcq
          // Characters of C(Q) -> corresponding characters of C(Y), the
          // character positions affected being specified in the TAG field.
          //copyChars (i->tag, cpu_p->rQ, &cpu_p->CY);
          cpu_p->CY = cpu_p->rQ;
          cpu_p->zone =
             ((i->tag & 040) ? 0770000000000u : 0) |
             ((i->tag & 020) ? 0007700000000u : 0) |
             ((i->tag & 010) ? 0000077000000u : 0) |
             ((i->tag & 004) ? 0000000770000u : 0) |
             ((i->tag & 002) ? 0000000007700u : 0) |
             ((i->tag & 001) ? 0000000000077u : 0);
          cpu_p->useZone = true;
          cpu_p->ou.crflag = true;
#ifdef TEST_OLIN
          cmpxchg ();
#endif
          break;

        case x0 (0357): //< stcd
          // C(PPR) -> C(Y-pair) as follows:

          //  000 -> C(Y-pair)0,2
          //  C(PPR.PSR) -> C(Y-pair)3,17
          //  C(PPR.PRR) -> C(Y-pair)18,20
          //  00...0 -> C(Y-pair)21,29
          //  (43)8 -> C(Y-pair)30,35

          //  C(PPR.IC)+2 -> C(Y-pair)36,53
          //  00...0 -> C(Y-pair)54,71

          // ISOLTS 880 5a has an STCD in an XED in a fault pair;
          // it reports the wrong ring number. This was fixed by
          // emulating the SCU instruction (different behavior in fault
          // pair).

          if (cpu_p->cycle == EXEC_cycle)
            {
              cpu_p->Ypair[0] = 0;
              putbits36_15 (& cpu_p->Ypair[0],  3, cpu_p->PPR.PSR);
              putbits36_3  (& cpu_p->Ypair[0], 18, cpu_p->PPR.PRR);
              putbits36_6  (& cpu_p->Ypair[0], 30, 043);

              cpu_p->Ypair[1] = 0;
              putbits36_18 (& cpu_p->Ypair[1],  0, cpu_p->PPR.IC + 2);
            }
          else
            {
              cpu_p->Ypair[0] = 0;
              putbits36_15 (& cpu_p->Ypair[0],  3, cpu_p->cu_data.PSR);
              putbits36_3  (& cpu_p->Ypair[0], 18, cpu_p->cu_data.PRR);
              //putbits36_6  (& cpu_p->Ypair[0], 30, 043);

              cpu_p->Ypair[1] = 0;
              putbits36_18 (& cpu_p->Ypair[1],  0, cpu_p->cu_data.IC + 2);
            }
          break;


// Optimized to the top of the loop
//        case x0 (0754): // sti

// Optimized to the top of the loop
//         case x0 (0756): // stq

        case x0 (0454):  // stt
          CPTUR (cptUseTR);
#ifdef ISOLTS
          if (current_running_cpu_idx)
            cpu_p->CY = ((-- cpu_p->shadowTR) & MASK27) << 9;
          else
            cpu_p->CY = (cpu_p->rTR & MASK27) << 9;
#else
          cpu_p->CY = (cpu_p->rTR & MASK27) << 9;
#endif
          break;


// Optimized to the top of the loop
//                         // stxn
//        case x0 (0740):  // stx0
//        case x0 (0741):  // stx1
//        case x0 (0742):  // stx2
//        case x0 (0743):  // stx3
//        case x0 (0744):  // stx4
//        case x0 (0745):  // stx5
//        case x0 (0746):  // stx6
//        case x0 (0747):  // stx7

// Optimized to the top of the loop
//        case x0 (0450): // stz

                         // sxln
        case x0 (0440):  // sxl0
        case x0 (0441):  // sxl1
        case x0 (0442):  // sxl2
        case x0 (0443):  // sxl3
        case x0 (0444):  // sxl4
        case x0 (0445):  // sxl5
        case x0 (0446):  // sxl6
        case x0 (0447):  // sxl7
          //SETLO (cpu_p->CY, cpu_p->rX[opcode10 & 07]);
          cpu_p->CY = cpu_p->rX[opcode10 & 07];
          cpu_p->zone = 0000000777777;
          cpu_p->useZone = true;
          break;

        /// Fixed-Point Data Movement Shift

        case x0 (0775):  // alr
          {
              word36 tmp36 = cpu_p->TPR.CA & 0177;   // CY bits 11-17
              for (uint j = 0 ; j < tmp36 ; j++)
              {
                  bool a0 = cpu_p->rA & SIGN36;    // A0
                  cpu_p->rA <<= 1;               // shift left 1
                  if (a0)                 // rotate A0 -> A35
                      cpu_p->rA |= 1;
              }
              cpu_p->rA &= DMASK;    // keep to 36-bits
              HDBGRegA ();

              SC_I_ZERO (cpu_p->rA == 0);
              SC_I_NEG (cpu_p->rA & SIGN36);
          }
          break;

// Optimized to the top of the loop
//        case x0 (0735):  // als

        case x0 (0771):  // arl
          // Shift C(A) right the number of positions given in
          // C(TPR.CA)11,17; filling vacated positions with zeros.
          {
            cpu_p->rA &= DMASK; // Make sure the shifted in bits are 0
            word36 tmp36 = cpu_p->TPR.CA & 0177;   // CY bits 11-17

            cpu_p->rA >>= tmp36;
            cpu_p->rA &= DMASK;    // keep to 36-bits
            HDBGRegA ();

            SC_I_ZERO (cpu_p->rA == 0);
            SC_I_NEG (cpu_p->rA & SIGN36);
          }
          break;

        case x0 (0731):  // ars
          {
            // Shift C(A) right the number of positions given in
            // C(TPR.CA)11,17; filling vacated positions with initial C(A)0.

            cpu_p->rA &= DMASK; // Make sure the shifted in bits are 0
            word18 tmp18 = cpu_p->TPR.CA & 0177;   // CY bits 11-17

            bool a0 = cpu_p->rA & SIGN36;    // A0
            for (uint j = 0 ; j < tmp18 ; j ++)
              {
                cpu_p->rA >>= 1;               // shift right 1
                if (a0)                 // propagate sign bit
                    cpu_p->rA |= SIGN36;
              }
            cpu_p->rA &= DMASK;    // keep to 36-bits
            HDBGRegA ();

            SC_I_ZERO (cpu_p->rA == 0);
            SC_I_NEG (cpu_p->rA & SIGN36);
          }
          break;

        case x0 (0777):  // llr
          // Shift C(AQ) left by the number of positions given in
          // C(TPR.CA)11,17; entering each bit leaving AQ0 into AQ71.

          {
            word36 tmp36 = cpu_p->TPR.CA & 0177;      // CY bits 11-17
            for (uint j = 0 ; j < tmp36 ; j++)
              {
                bool a0 = cpu_p->rA & SIGN36;         // A0

                cpu_p->rA <<= 1;                      // shift left 1

                bool b0 = cpu_p->rQ & SIGN36;         // Q0
                if (b0)
                  cpu_p->rA |= 1;                     // Q0 => A35

                cpu_p->rQ <<= 1;                      // shift left 1

                if (a0)                            // propagate A sign bit
                  cpu_p->rQ |= 1;
              }

            cpu_p->rA &= DMASK;    // keep to 36-bits
            HDBGRegA ();
            cpu_p->rQ &= DMASK;
            HDBGRegQ ();

            SC_I_ZERO (cpu_p->rA == 0 && cpu_p->rQ == 0);
            SC_I_NEG (cpu_p->rA & SIGN36);
          }
          break;

        case x0 (0737):  // lls
          {
            // Shift C(AQ) left the number of positions given in
            // C(TPR.CA)11,17; filling vacated positions with zeros.

            CLR_I_CARRY;

            word36 tmp36 = cpu_p->TPR.CA & 0177;   // CY bits 11-17
            word36 tmpSign = cpu_p->rA & SIGN36;
            for (uint j = 0 ; j < tmp36 ; j ++)
              {
                cpu_p->rA <<= 1;               // shift left 1

                if (tmpSign != (cpu_p->rA & SIGN36))
                  SET_I_CARRY;

                bool b0 = cpu_p->rQ & SIGN36;    // Q0
                if (b0)
                  cpu_p->rA |= 1;            // Q0 => A35

                cpu_p->rQ <<= 1;               // shift left 1
              }

            cpu_p->rA &= DMASK;    // keep to 36-bits
            HDBGRegA ();
            cpu_p->rQ &= DMASK;
            HDBGRegQ ();

            SC_I_ZERO (cpu_p->rA == 0 && cpu_p->rQ == 0);
            SC_I_NEG (cpu_p->rA & SIGN36);
          }
          break;

        case x0 (0773):  // lrl
          // Shift C(AQ) right the number of positions given in
          // C(TPR.CA)11,17; filling vacated positions with zeros.
          {
            cpu_p->rA &= DMASK; // Make sure the shifted in bits are 0
            cpu_p->rQ &= DMASK; // Make sure the shifted in bits are 0
            word36 tmp36 = cpu_p->TPR.CA & 0177;   // CY bits 11-17
            for (uint j = 0 ; j < tmp36 ; j++)
              {
                bool a35 = cpu_p->rA & 1;      // A35
                cpu_p->rA >>= 1;               // shift right 1

                cpu_p->rQ >>= 1;               // shift right 1

                if (a35)                // propagate sign bit
                  cpu_p->rQ |= SIGN36;
              }
            cpu_p->rA &= DMASK;    // keep to 36-bits
            HDBGRegA ();
            cpu_p->rQ &= DMASK;
            HDBGRegQ ();

            SC_I_ZERO (cpu_p->rA == 0 && cpu_p->rQ == 0);
            SC_I_NEG (cpu_p->rA & SIGN36);
          }
          break;

        case x0 (0733):  // lrs
          {
            // Shift C(AQ) right the number of positions given in
            // C(TPR.CA)11,17; filling vacated positions with initial C(AQ)0.

            word36 tmp36 = cpu_p->TPR.CA & 0177;   // CY bits 11-17
            cpu_p->rA &= DMASK; // Make sure the shifted in bits are 0
            cpu_p->rQ &= DMASK; // Make sure the shifted in bits are 0
            bool a0 = cpu_p->rA & SIGN36;    // A0

            for (uint j = 0 ; j < tmp36 ; j ++)
              {
                bool a35 = cpu_p->rA & 1;      // A35

                cpu_p->rA >>= 1;               // shift right 1
                if (a0)
                  cpu_p->rA |= SIGN36;

                cpu_p->rQ >>= 1;               // shift right 1
                if (a35)                // propagate sign bit1
                  cpu_p->rQ |= SIGN36;
              }
            cpu_p->rA &= DMASK;    // keep to 36-bits (probably ain't necessary)
            HDBGRegA ();
            cpu_p->rQ &= DMASK;
            HDBGRegQ ();

            SC_I_ZERO (cpu_p->rA == 0 && cpu_p->rQ == 0);
            SC_I_NEG (cpu_p->rA & SIGN36);
          }
          break;

        case x0 (0776):  // qlr
          // Shift C(Q) left the number of positions given in
          // C(TPR.CA)11,17; entering each bit leaving Q0 into Q35.
          {
            word36 tmp36 = cpu_p->TPR.CA & 0177;   // CY bits 11-17
            for (uint j = 0 ; j < tmp36 ; j++)
              {
                bool q0 = cpu_p->rQ & SIGN36;    // Q0
                cpu_p->rQ <<= 1;               // shift left 1
                if (q0)                 // rotate A0 -> A35
                  cpu_p->rQ |= 1;
              }
            cpu_p->rQ &= DMASK;    // keep to 36-bits
            HDBGRegQ ();

            SC_I_ZERO (cpu_p->rQ == 0);
            SC_I_NEG (cpu_p->rQ & SIGN36);
          }
          break;

// Optimized to the top of the loop
//        case x0 (0736):  // qls

        case x0 (0772):  // qrl
          // Shift C(Q) right the number of positions specified by
          // Y11,17; fill vacated positions with zeros.
          {
            word36 tmp36 = cpu_p->TPR.CA & 0177;   // CY bits 11-17

            cpu_p->rQ &= DMASK;    // Make sure the shifted in bits are 0
            cpu_p->rQ >>= tmp36;
            cpu_p->rQ &= DMASK;    // keep to 36-bits
            HDBGRegQ ();

            SC_I_ZERO (cpu_p->rQ == 0);
            SC_I_NEG (cpu_p->rQ & SIGN36);

          }
          break;

        case x0 (0732):  // qrs
          {
            // Shift C(Q) right the number of positions given in
            // C(TPR.CA)11,17; filling vacated positions with initial C(Q)0.

            cpu_p->rQ &= DMASK; // Make sure the shifted in bits are 0
            word36 tmp36 = cpu_p->TPR.CA & 0177;   // CY bits 11-17
            bool q0 = cpu_p->rQ & SIGN36;    // Q0
            for (uint j = 0 ; j < tmp36 ; j++)
              {
                cpu_p->rQ >>= 1;               // shift right 1
                if (q0)                 // propagate sign bit
                  cpu_p->rQ |= SIGN36;
              }
            cpu_p->rQ &= DMASK;    // keep to 36-bits
            HDBGRegQ ();

            SC_I_ZERO (cpu_p->rQ == 0);
            SC_I_NEG (cpu_p->rQ & SIGN36);
          }
          break;

        /// Fixed-Point Addition

        case x0 (0075):  // ada
          {
            // C(A) + C(Y) -> C(A)
            // Modifications: All
            //
            //  (Indicators not listed are not affected)
            //  ZERO: If C(A) = 0, then ON; otherwise OFF
            //  NEG: If C(A)0 = 1, then ON; otherwise OFF
            //  OVR: If range of A is exceeded, then ON
            //  CARRY: If a carry out of A0 is generated, then ON; otherwise OFF

#ifdef L68
            cpu_p->ou.cycle |= ou_GOS;
#endif
            bool ovf;
            cpu_p->rA = Add36b (cpu_p->rA, cpu_p->CY, 0, I_ZNOC, & cpu_p->cu.IR, & ovf);
            HDBGRegA ();
            overflow (cpu_p, ovf, false, "ada overflow fault");
          }
#ifdef TEST_OLIN
          cmpxchg ();
#endif
          break;

        case x0 (0077):   // adaq
          {
            // C(AQ) + C(Y-pair) -> C(AQ)
#ifdef L68
            cpu_p->ou.cycle |= ou_GOS;
#endif
            bool ovf;
            word72 tmp72 = YPAIRTO72 (cpu_p->Ypair);
            tmp72 = Add72b (convert_to_word72 (cpu_p->rA, cpu_p->rQ), tmp72, 0,
                            I_ZNOC, & cpu_p->cu.IR, & ovf);
            convert_to_word36 (tmp72, & cpu_p->rA, & cpu_p->rQ);
            HDBGRegA ();
            HDBGRegQ ();
            overflow (cpu_p, ovf, false, "adaq overflow fault");
          }
          break;

        case x0 (0033):   // adl
          {
            // C(AQ) + C(Y) sign extended -> C(AQ)
#ifdef L68
            cpu_p->ou.cycle |= ou_GOS;
#endif
            bool ovf;
            word72 tmp72 = SIGNEXT36_72 (cpu_p->CY); // sign extend Cy
            tmp72 = Add72b (convert_to_word72 (cpu_p->rA, cpu_p->rQ), tmp72, 0,
                            I_ZNOC,
                            & cpu_p->cu.IR, & ovf);
            convert_to_word36 (tmp72, & cpu_p->rA, & cpu_p->rQ);
            HDBGRegA ();
            HDBGRegQ ();
            overflow (cpu_p, ovf, false, "adl overflow fault");
          }
          break;


        case x0 (0037):   // adlaq
          {
            // The adlaq instruction is identical to the adaq instruction with
            // the exception that the overflow indicator is not affected by the
            // adlaq instruction, nor does an overflow fault occur. Operands
            // and results are treated as unsigned, positive binary integers.
#ifdef L68
            cpu_p->ou.cycle |= ou_GOS;
#endif
            bool ovf;
            word72 tmp72 = YPAIRTO72 (cpu_p->Ypair);

            tmp72 = Add72b (convert_to_word72 (cpu_p->rA, cpu_p->rQ), tmp72, 0,
                            I_ZNC, & cpu_p->cu.IR, & ovf);
            convert_to_word36 (tmp72, & cpu_p->rA, & cpu_p->rQ);
            HDBGRegA ();
            HDBGRegQ ();
          }
          break;

        case x0 (0035):   // adla
          {
#ifdef L68
            cpu_p->ou.cycle |= ou_GOS;
#endif
            // The adla instruction is identical to the ada instruction with
            // the exception that the overflow indicator is not affected by the
            // adla instruction, nor does an overflow fault occur. Operands and
            // results are treated as unsigned, positive binary integers. */

            bool ovf;
            cpu_p->rA = Add36b (cpu_p->rA, cpu_p->CY, 0, I_ZNC, & cpu_p->cu.IR, & ovf);
            HDBGRegA ();
          }
          break;

        case x0 (0036):   // adlq
          {
            // The adlq instruction is identical to the adq instruction with
            // the exception that the overflow indicator is not affected by the
            // adlq instruction, nor does an overflow fault occur. Operands and
            // results are treated as unsigned, positive binary integers. */

#ifdef L68
            cpu_p->ou.cycle |= ou_GOS;
#endif
            bool ovf;
            cpu_p->rQ = Add36b (cpu_p->rQ, cpu_p->CY, 0, I_ZNC, & cpu_p->cu.IR, & ovf);
            HDBGRegQ ();
          }
          break;

                          // adlxn
        case x0 (0020):   // adlx0
        case x0 (0021):   // adlx1
        case x0 (0022):   // adlx2
        case x0 (0023):   // adlx3
        case x0 (0024):   // adlx4
        case x0 (0025):   // adlx5
        case x0 (0026):   // adlx6
        case x0 (0027):   // adlx7
          {
#ifdef L68
            cpu_p->ou.cycle |= ou_GOS;
#endif
            bool ovf;
            uint32 n = opcode10 & 07;  // get n
            cpu_p->rX[n] = Add18b (cpu_p->rX[n], GETHI (cpu_p->CY), 0, I_ZNC,
                             & cpu_p->cu.IR, & ovf);
            HDBGRegX (n);
          }
          break;

// Optimized to the top of the loop
//        case x0 (0076):   // adq

                          // adxn
        case x0 (0060):   // adx0
        case x0 (0061):   // adx1
        case x0 (0062):   // adx2
        case x0 (0063):   // adx3
        case x0 (0064):   // adx4
        case x0 (0065):   // adx5
        case x0 (0066):   // adx6
        case x0 (0067):   // adx7
          {
#ifdef L68
            cpu_p->ou.cycle |= ou_GOS;
#endif
            bool ovf;
            uint32 n = opcode10 & 07;  // get n
            cpu_p->rX[n] = Add18b (cpu_p->rX[n], GETHI (cpu_p->CY), 0,
                                 I_ZNOC,
                                 & cpu_p->cu.IR, & ovf);
            HDBGRegX (n);
            overflow (cpu_p, ovf, false, "adxn overflow fault");
          }
          break;

// Optimized to the top of the loop
//        case x0 (0054):   // aos

        case x0 (0055):   // asa
          {
            // C(A) + C(Y) -> C(Y)

#ifdef L68
            cpu_p->ou.cycle |= ou_GOS;
#endif
            bool ovf;
            cpu_p->CY = Add36b (cpu_p->rA, cpu_p->CY, 0, I_ZNOC,
                             & cpu_p->cu.IR, & ovf);
            HDBGRegA ();
            overflow (cpu_p, ovf, true, "asa overflow fault");
          }
#ifdef TEST_OLIN
          cmpxchg ();
#endif
          break;

        case x0 (0056):   // asq
          {
            // C(Q) + C(Y) -> C(Y)
#ifdef L68
            cpu_p->ou.cycle |= ou_GOS;
#endif
            bool ovf;
            cpu_p->CY = Add36b (cpu_p->rQ, cpu_p->CY, 0, I_ZNOC, & cpu_p->cu.IR, & ovf);
            overflow (cpu_p, ovf, true, "asq overflow fault");
          }
#ifdef TEST_OLIN
          cmpxchg ();
#endif
          break;

                          // asxn
        case x0 (0040):   // asx0
        case x0 (0041):   // asx1
        case x0 (0042):   // asx2
        case x0 (0043):   // asx3
        case x0 (0044):   // asx4
        case x0 (0045):   // asx5
        case x0 (0046):   // asx6
        case x0 (0047):   // asx7
          {
            // For n = 0, 1, ..., or 7 as determined by operation code
            //    C(Xn) + C(Y)0,17 -> C(Y)0,17
#ifdef L68
            cpu_p->ou.cycle |= ou_GOS;
#endif
            bool ovf;
            uint32 n = opcode10 & 07;  // get n
            word18 tmp18 = Add18b (cpu_p->rX[n], GETHI (cpu_p->CY), 0,
                                   I_ZNOC, & cpu_p->cu.IR, & ovf);
            SETHI (cpu_p->CY, tmp18);
            overflow (cpu_p, ovf, true, "asxn overflow fault");
#ifdef TEST_OLIN
          cmpxchg ();
#endif
          }
          break;

        case x0 (0071):   // awca
          {
            // If carry indicator OFF, then C(A) + C(Y) -> C(A)
            // If carry indicator ON, then C(A) + C(Y) + 1 -> C(A)

#ifdef L68
            cpu_p->ou.cycle |= ou_GOS;
#endif
            bool ovf;
            cpu_p->rA = Add36b (cpu_p->rA, cpu_p->CY, TST_I_CARRY ? 1 : 0,
                                 I_ZNOC, & cpu_p->cu.IR, & ovf);
            HDBGRegA ();
            overflow (cpu_p, ovf, false, "awca overflow fault");
          }
          break;

        case x0 (0072):   // awcq
          {
            // If carry indicator OFF, then C(Q) + C(Y) -> C(Q)
            // If carry indicator ON, then C(Q) + C(Y) + 1 -> C(Q)

#ifdef L68
            cpu_p->ou.cycle |= ou_GOS;
#endif
            bool ovf;
            cpu_p->rQ = Add36b (cpu_p->rQ, cpu_p->CY, TST_I_CARRY ? 1 : 0,
                             I_ZNOC, & cpu_p->cu.IR, & ovf);
            HDBGRegQ ();
            overflow (cpu_p, ovf, false, "awcq overflow fault");
          }
          break;

        /// Fixed-Point Subtraction

        case x0 (0175):  // sba
          {
            // C(A) - C(Y) -> C(A)

#ifdef L68
            cpu_p->ou.cycle |= ou_GOS;
#endif
            bool ovf;
            cpu_p->rA = Sub36b (cpu_p->rA, cpu_p->CY, 1, I_ZNOC, & cpu_p->cu.IR, & ovf);
            HDBGRegA ();
            overflow (cpu_p, ovf, false, "sba overflow fault");
          }
          break;

        case x0 (0177):  // sbaq
          {
            // C(AQ) - C(Y-pair) -> C(AQ)
#ifdef L68
            cpu_p->ou.cycle |= ou_GOS;
#endif
            bool ovf;
            word72 tmp72 = YPAIRTO72 (cpu_p->Ypair);
            tmp72 = Sub72b (convert_to_word72 (cpu_p->rA, cpu_p->rQ), tmp72, 1,
                            I_ZNOC, & cpu_p->cu.IR,
                            & ovf);
            convert_to_word36 (tmp72, & cpu_p->rA, & cpu_p->rQ);
            HDBGRegA ();
            HDBGRegQ ();
            overflow (cpu_p, ovf, false, "sbaq overflow fault");
          }
          break;

        case x0 (0135):  // sbla
          {
            // C(A) - C(Y) -> C(A) logical

#ifdef L68
            cpu_p->ou.cycle |= ou_GOS;
#endif
            bool ovf;
            cpu_p->rA = Sub36b (cpu_p->rA, cpu_p->CY, 1, I_ZNC, & cpu_p->cu.IR, & ovf);
            HDBGRegA ();
          }
          break;

        case x0 (0137):  // sblaq
          {
            // The sblaq instruction is identical to the sbaq instruction with
            // the exception that the overflow indicator is not affected by the
            // sblaq instruction, nor does an overflow fault occur. Operands
            // and results are treated as unsigned, positive binary integers.
            // C(AQ) - C(Y-pair) -> C(AQ)

#ifdef L68
            cpu_p->ou.cycle |= ou_GOS;
#endif
            bool ovf;
            word72 tmp72 = YPAIRTO72 (cpu_p->Ypair);

            tmp72 = Sub72b (convert_to_word72 (cpu_p->rA, cpu_p->rQ), tmp72, 1,
                            I_ZNC, & cpu_p->cu.IR, & ovf);
            convert_to_word36 (tmp72, & cpu_p->rA, & cpu_p->rQ);
            HDBGRegA ();
            HDBGRegQ ();
          }
          break;

        case x0 (0136):  // sblq
          {
            // C(Q) - C(Y) -> C(Q)
#ifdef L68
            cpu_p->ou.cycle |= ou_GOS;
#endif
            bool ovf;
            cpu_p->rQ = Sub36b (cpu_p->rQ, cpu_p->CY, 1, I_ZNC, & cpu_p->cu.IR, & ovf);
            HDBGRegQ ();
          }
          break;

                         // sblxn
        case x0 (0120):  // sblx0
        case x0 (0121):  // sblx1
        case x0 (0122):  // sblx2
        case x0 (0123):  // sblx3
        case x0 (0124):  // sblx4
        case x0 (0125):  // sblx5
        case x0 (0126):  // sblx6
        case x0 (0127):  // sblx7
          {
            // For n = 0, 1, ..., or 7 as determined by operation code
            // C(Xn) - C(Y)0,17 -> C(Xn)

#ifdef L68
            cpu_p->ou.cycle |= ou_GOS;
#endif
            bool ovf;
            uint32 n = opcode10 & 07;  // get n
            cpu_p->rX[n] = Sub18b (cpu_p->rX[n], GETHI (cpu_p->CY), 1,
                             I_ZNC, & cpu_p->cu.IR, & ovf);
            HDBGRegX (n);
          }
          break;

        case x0 (0176):  // sbq
          {
            // C(Q) - C(Y) -> C(Q)
#ifdef L68
            cpu_p->ou.cycle |= ou_GOS;
#endif
            bool ovf;
            cpu_p->rQ = Sub36b (cpu_p->rQ, cpu_p->CY, 1, I_ZNOC, & cpu_p->cu.IR, & ovf);
            HDBGRegQ ();
            overflow (cpu_p, ovf, false, "sbq overflow fault");
          }
          break;

                         // sbxn
        case x0 (0160):  // sbx0
        case x0 (0161):  // sbx1
        case x0 (0162):  // sbx2
        case x0 (0163):  // sbx3
        case x0 (0164):  // sbx4
        case x0 (0165):  // sbx5
        case x0 (0166):  // sbx6
        case x0 (0167):  // sbx7
          {
            // For n = 0, 1, ..., or 7 as determined by operation code
            // C(Xn) - C(Y)0,17 -> C(Xn)

#ifdef L68
            cpu_p->ou.cycle |= ou_GOS;
#endif
            bool ovf;
            uint32 n = opcode10 & 07;  // get n
            cpu_p->rX[n] = Sub18b (cpu_p->rX[n], GETHI (cpu_p->CY), 1,
                                 I_ZNOC, & cpu_p->cu.IR, & ovf);
            HDBGRegX (n);
            overflow (cpu_p, ovf, false, "sbxn overflow fault");
          }
          break;

        case x0 (0155):  // ssa
          {
            // C(A) - C(Y) -> C(Y)

#ifdef L68
            cpu_p->ou.cycle |= ou_GOS;
#endif
            bool ovf;
            cpu_p->CY = Sub36b (cpu_p->rA, cpu_p->CY, 1, I_ZNOC, & cpu_p->cu.IR, & ovf);
            overflow (cpu_p, ovf, true, "ssa overflow fault");
          }
#ifdef TEST_OLIN
          cmpxchg ();
#endif
          break;

        case x0 (0156):  // ssq
          {
            // C(Q) - C(Y) -> C(Y)

#ifdef L68
            cpu_p->ou.cycle |= ou_GOS;
#endif
            bool ovf;
            cpu_p->CY = Sub36b (cpu_p->rQ, cpu_p->CY, 1, I_ZNOC, & cpu_p->cu.IR, & ovf);
            overflow (cpu_p, ovf, true, "ssq overflow fault");
          }
#ifdef TEST_OLIN
          cmpxchg ();
#endif
          break;

                         // ssxn
        case x0 (0140):  // ssx0
        case x0 (0141):  // ssx1
        case x0 (0142):  // ssx2
        case x0 (0143):  // ssx3
        case x0 (0144):  // ssx4
        case x0 (0145):  // ssx5
        case x0 (0146):  // ssx6
        case x0 (0147):  // ssx7
          {
            // For uint32 n = 0, 1, ..., or 7 as determined by operation code
            // C(Xn) - C(Y)0,17 -> C(Y)0,17

#ifdef L68
            cpu_p->ou.cycle |= ou_GOS;
#endif
            bool ovf;
            uint32 n = opcode10 & 07;  // get n
            word18 tmp18 = Sub18b (cpu_p->rX[n], GETHI (cpu_p->CY), 1,
                                   I_ZNOC, & cpu_p->cu.IR, & ovf);
            SETHI (cpu_p->CY, tmp18);
            overflow (cpu_p, ovf, true, "ssxn overflow fault");
          }
#ifdef TEST_OLIN
          cmpxchg ();
#endif
          break;


        case x0 (0171):  // swca
          {
            // If carry indicator ON, then C(A)- C(Y) -> C(A)
            // If carry indicator OFF, then C(A) - C(Y) - 1 -> C(A)

#ifdef L68
            cpu_p->ou.cycle |= ou_GOS;
#endif
            bool ovf;
            cpu_p->rA = Sub36b (cpu_p->rA, cpu_p->CY, TST_I_CARRY ? 1 : 0,
                             I_ZNOC, & cpu_p->cu.IR, & ovf);
            HDBGRegA ();
            overflow (cpu_p, ovf, false, "swca overflow fault");
          }
          break;

        case x0 (0172):  // swcq
          {
            // If carry indicator ON, then C(Q) - C(Y) -> C(Q)
            // If carry indicator OFF, then C(Q) - C(Y) - 1 -> C(Q)

#ifdef L68
            cpu_p->ou.cycle |= ou_GOS;
#endif
            bool ovf;
            cpu_p->rQ = Sub36b (cpu_p->rQ, cpu_p->CY, TST_I_CARRY ? 1 : 0,
                                 I_ZNOC, & cpu_p->cu.IR, & ovf);
            HDBGRegQ ();
            overflow (cpu_p, ovf, false, "swcq overflow fault");
          }
          break;

        /// Fixed-Point Multiplication

        case x0 (0401):  // mpf
          {
            // C(A) * C(Y) -> C(AQ), left adjusted
            //
            // Two 36-bit fractional factors (including sign) are multiplied
            // to form a 71- bit fractional product (including sign), which
            // is stored left-adjusted in the AQ register. AQ71 contains a
            // zero. Overflow can occur only in the case of A and Y
            // containing negative 1 and the result exceeding the range of
            // the AQ register.

#ifdef L68
            cpu_p->ou.cycle |= ou_GD1;
#endif
#ifdef NEED_128
            word72 tmp72 = multiply_128 (SIGNEXT36_72 (cpu_p->rA), SIGNEXT36_72 (cpu_p->CY));
            tmp72 = and_128 (tmp72, MASK72);
            tmp72 = lshift_128 (tmp72, 1);
#else
            word72 tmp72 = SIGNEXT36_72 (cpu_p->rA) * SIGNEXT36_72 (cpu_p->CY);
            tmp72 &= MASK72;
            tmp72 <<= 1;    // left adjust so AQ71 contains 0
#endif
#ifdef L68
            cpu_p->ou.cycle |= ou_GD2;
#endif
            // Overflow can occur only in the case of A and Y containing
            // negative 1
            if (cpu_p->rA == MAXNEG && cpu_p->CY == MAXNEG)
              {
                SET_I_NEG;
                CLR_I_ZERO;
                overflow (cpu_p, true, false, "mpf overflow fault");
              }

            convert_to_word36 (tmp72, &cpu_p->rA, &cpu_p->rQ);
            HDBGRegA ();
            HDBGRegQ ();
            SC_I_ZERO (cpu_p->rA == 0 && cpu_p->rQ == 0);
            SC_I_NEG (cpu_p->rA & SIGN36);
          }
          break;

        case x0 (0402):  // mpy
          // C(Q) * C(Y) -> C(AQ), right adjusted

          {
#ifdef L68
            cpu_p->ou.cycle |= ou_GOS;
#endif
#ifdef NEED_128
            int128 prod = multiply_s128 (
              SIGNEXT36_128 (cpu_p->rQ & DMASK),
              SIGNEXT36_128 (cpu_p->CY & DMASK));
            convert_to_word36 (cast_128 (prod), &cpu_p->rA, &cpu_p->rQ);
#else
            int64_t t0 = SIGNEXT36_64 (cpu_p->rQ & DMASK);
            int64_t t1 = SIGNEXT36_64 (cpu_p->CY & DMASK);

            __int128_t prod = (__int128_t) t0 * (__int128_t) t1;

            convert_to_word36 ((word72)prod, &cpu_p->rA, &cpu_p->rQ);
#endif
            HDBGRegA ();
            HDBGRegQ ();

            SC_I_ZERO (cpu_p->rA == 0 && cpu_p->rQ == 0);
            SC_I_NEG (cpu_p->rA & SIGN36);
          }
          break;

//#define DIV_TRACE

        /// Fixed-Point Division

        case x0 (0506):  // div
          // C(Q) / (Y) integer quotient -> C(Q), integer remainder -> C(A)
          //
          // A 36-bit integer dividend (including sign) is divided by a
          // 36-bit integer divisor (including sign) to form a 36-bit integer
          // * quotient (including sign) and a 36-bit integer remainder
          // * (including sign). The remainder sign is equal to the dividend
          // * sign unless the remainder is zero.
          // *
          // * If the dividend = -2**35 and the divisor = -1 or if the divisor
          // * = 0, then division does not take place. Instead, a divide check
          // * fault occurs, C(Q) contains the dividend magnitude, and the
          // * negative indicator reflects the dividend sign.

#ifdef L68
          cpu_p->ou.cycle |= ou_GD1;
#endif
          // RJ78: If the dividend = -2**35 and the divisor = +/-1, or if 
          // the divisor is 0

          if ((cpu_p->rQ == MAXNEG && (cpu_p->CY == 1 || cpu_p->CY == NEG136)) ||
              (cpu_p->CY == 0))
            {
//sim_printf ("DIV Q %012"PRIo64" Y %012"PRIo64"\n", cpu_p->rQ, cpu_p->CY); 
// case 1  400000000000 000000000000 --> 000000000000
// case 2  000000000000 000000000000 --> 400000000000
              //cpu_p->rA = 0;  // works for case 1
              cpu_p->rA = (cpu_p->rQ & SIGN36) ? 0 : SIGN36; // works for case 1,2
              HDBGRegA ();

              // no division takes place
              SC_I_ZERO (cpu_p->CY == 0);
              SC_I_NEG (cpu_p->rQ & SIGN36);

              if (cpu_p->rQ & SIGN36)
                {
                  cpu_p->rQ = (- cpu_p->rQ) & MASK36;
                  HDBGRegQ ();
                }

              dlyDoFault (cpu_p, FAULT_DIV,
                          fst_ill_op,
                          "div divide check");
            }
          else
            {
              t_int64 dividend = (t_int64) (SIGNEXT36_64 (cpu_p->rQ));
              t_int64 divisor = (t_int64) (SIGNEXT36_64 (cpu_p->CY));

#ifdef DIV_TRACE
              sim_debug (DBG_CAC, & cpu_dev, "\n");
              sim_debug (DBG_CAC, & cpu_dev,
                         ">>> dividend cpu_p->rQ %"PRId64" (%012"PRIo64")\n",
                         dividend, cpu_p->rQ);
              sim_debug (DBG_CAC, & cpu_dev,
                         ">>> divisor  CY %"PRId64" (%012"PRIo64")\n",
                         divisor, cpu_p->CY);
#endif

              t_int64 quotient = dividend / divisor;
#ifdef L68
              cpu_p->ou.cycle |= ou_GD2;
#endif
              t_int64 remainder = dividend % divisor;

#ifdef DIV_TRACE
              sim_debug (DBG_CAC, & cpu_dev, ">>> quot 1 %"PRId64"\n", quotient);
              sim_debug (DBG_CAC, & cpu_dev, ">>> rem 1 %"PRId64"\n", remainder);
#endif

// Evidence is that DPS8M rounds toward zero; if it turns out that it
// rounds toward -inf, try this code:
#if 0
              // XXX C rounds toward zero; I suspect that DPS8M rounded toward
              // -inf.
              // If the remainder is negative, we rounded the wrong way
              if (remainder < 0)
                {
                  remainder += divisor;
                  quotient -= 1;

#ifdef DIV_TRACE
                  sim_debug (DBG_CAC, & cpu_dev,
                             ">>> quot 2 %"PRId64"\n", quotient);
                  sim_debug (DBG_CAC, & cpu_dev,
                             ">>> rem 2 %"PRId64"\n", remainder);
#endif
                }
#endif

#ifdef DIV_TRACE
              //  (a/b)*b + a%b is equal to a.
              sim_debug (DBG_CAC, & cpu_dev,
                         "dividend was                   = %"PRId64"\n", dividend);
              sim_debug (DBG_CAC, & cpu_dev,
                         "quotient * divisor + remainder = %"PRId64"\n",
                         quotient * divisor + remainder);
              if (dividend != quotient * divisor + remainder)
                {
                  sim_debug (DBG_CAC, & cpu_dev,
                     "---------------------------------^^^^^^^^^^^^^^^\n");
                }
#endif


              if (dividend != quotient * divisor + remainder)
                {
                  sim_debug (DBG_ERR, & cpu_dev,
                             "Internal division error;"
                             " rQ %012"PRIo64" CY %012"PRIo64"\n", cpu_p->rQ, cpu_p->CY);
                }

              cpu_p->rA = (word36) remainder & DMASK;
              HDBGRegA ();
              cpu_p->rQ = (word36) quotient & DMASK;
              HDBGRegQ ();

#ifdef DIV_TRACE
              sim_debug (DBG_CAC, & cpu_dev, "rA (rem)  %012"PRIo64"\n", cpu_p->rA);
              sim_debug (DBG_CAC, & cpu_dev, "rQ (quot) %012"PRIo64"\n", cpu_p->rQ);
#endif

              SC_I_ZERO (cpu_p->rQ == 0);
              SC_I_NEG (cpu_p->rQ & SIGN36);
            }

          break;

        case x0 (0507):  // dvf
          // C(AQ) / (Y)
          //  fractional quotient -> C(A)
          //  fractional remainder -> C(Q)

          // A 71-bit fractional dividend (including sign) is divided by a
          // 36-bit fractional divisor yielding a 36-bit fractional quotient
          // (including sign) and a 36-bit fractional remainder (including
          // sign). C(AQ)71 is ignored; bit position 35 of the remainder
          // corresponds to bit position 70 of the dividend. The remainder
          // sign is equal to the dividend sign unless the remainder is zero.

          // If | dividend | >= | divisor | or if the divisor = 0, division
          // does not take place. Instead, a divide check fault occurs, C(AQ)
          // contains the dividend magnitude in absolute, and the negative
          // indicator reflects the dividend sign.

          dvf ();

          break;

        /// Fixed-Point Negate

        case x0 (0531):  // neg
          // -C(A) -> C(A) if C(A) != 0

          cpu_p->rA &= DMASK;
          if (cpu_p->rA == 0400000000000ULL)
            {
              CLR_I_ZERO;
              SET_I_NEG;
              overflow (cpu_p, true, false, "neg overflow fault");
            }

          cpu_p->rA = -cpu_p->rA;

          cpu_p->rA &= DMASK;    // keep to 36-bits
          HDBGRegA ();

          SC_I_ZERO (cpu_p->rA == 0);
          SC_I_NEG (cpu_p->rA & SIGN36);

          break;

        case x0 (0533):  // negl
          // -C(AQ) -> C(AQ) if C(AQ) != 0
          {
            cpu_p->rA &= DMASK;
            cpu_p->rQ &= DMASK;

            if (cpu_p->rA == 0400000000000ULL && cpu_p->rQ == 0)
            {
                CLR_I_ZERO;
                SET_I_NEG;
                overflow (cpu_p, true, false, "negl overflow fault");
            }

            word72 tmp72 = convert_to_word72 (cpu_p->rA, cpu_p->rQ);
#ifdef NEED_128
            tmp72 = negate_128 (tmp72);

            SC_I_ZERO (iszero_128 (tmp72));
            SC_I_NEG (isnonzero_128 (and_128 (tmp72, SIGN72)));
#else
            tmp72 = -tmp72;

            SC_I_ZERO (tmp72 == 0);
            SC_I_NEG (tmp72 & SIGN72);
#endif

            convert_to_word36 (tmp72, &cpu_p->rA, &cpu_p->rQ);
            HDBGRegA ();
            HDBGRegQ ();
          }
          break;

        /// Fixed-Point Comparison

        case x0 (0405):  // cmg
          // | C(A) | :: | C(Y) |
          // Zero:     If | C(A) | = | C(Y) | , then ON; otherwise OFF
          // Negative: If | C(A) | < | C(Y) | , then ON; otherwise OFF
          {
            // This is wrong for MAXNEG
            //word36 a = cpu_p->rA & SIGN36 ? -cpu_p->rA : cpu_p->rA;
            //word36 y = cpu_p->CY & SIGN36 ? -cpu_p->CY : cpu_p->CY;

              // If we do the 64 math, the MAXNEG case works
              t_int64 a = SIGNEXT36_64 (cpu_p->rA);
              if (a < 0)
                a = -a;
              t_int64 y = SIGNEXT36_64 (cpu_p->CY);
              if (y < 0)
                y = -y;

              SC_I_ZERO (a == y);
              SC_I_NEG (a < y);
          }
          break;

        case x0 (0211):  // cmk
          // For i = 0, 1, ..., 35
          // C(Z)i = ~C(Q)i & ( C(A)i XOR C(Y)i )

          /**
           * The cmk instruction compares the contents of bit positions of A
           * and Y for identity that are not masked by a 1 in the
           * corresponding bit position of Q.
           *
           * The zero indicator is set ON if the comparison is successful for
           * all bit positions; i.e., if for all i = 0, 1, ..., 35 there is
           * either: C(A)i = C(Y)i (the identical case) or C(Q)i = 1 (the
           * masked case); otherwise, the zero indicator is set OFF.
           *
           * The negative indicator is set ON if the comparison is
           * unsuccessful for bit position 0; i.e., if C(A)0 XOR C(Y)0 (they
           * are nonidentical) as well as C(Q)0 = 0 (they are unmasked);
           * otherwise, the negative indicator is set OFF.
           */
          {
            word36 Z = ~cpu_p->rQ & (cpu_p->rA ^ cpu_p->CY);
            Z &= DMASK;

// Q  A  Y   ~Q   A^Y   Z
// 0  0  0    1     0   0
// 0  0  1    1     1   1
// 0  1  0    1     1   1
// 0  1  1    1     0   0
// 1  0  0    0     0   0
// 1  0  1    0     1   0
// 1  1  0    0     1   0
// 1  1  1    0     0   0


            SC_I_ZERO (Z == 0);
            SC_I_NEG (Z & SIGN36);
          }
          break;

// Optimized to the top of the loop
//        case x0 (0115):  // cmpa

        case x0 (0117):  // cmpaq
          // C(AQ) :: C(Y-pair)
          {
            word72 tmp72 = YPAIRTO72 (cpu_p->Ypair);
            word72 trAQ = convert_to_word72 (cpu_p->rA, cpu_p->rQ);
#ifdef NEED_128
            trAQ = and_128 (trAQ, MASK72);
#else
            trAQ &= MASK72;
#endif
            cmp72 (trAQ, tmp72, &cpu_p->cu.IR);
          }
          break;

// Optimized to the top of the loop
//         case x0 (0116):  // cmpq

                         // cmpxn
        case x0 (0100):  // cmpx0
        case x0 (0101):  // cmpx1
        case x0 (0102):  // cmpx2
        case x0 (0103):  // cmpx3
        case x0 (0104):  // cmpx4
        case x0 (0105):  // cmpx5
        case x0 (0106):  // cmpx6
        case x0 (0107):  // cmpx7
          // For n = 0, 1, ..., or 7 as determined by operation code
          // C(Xn) :: C(Y)0,17
          {
            uint32 n = opcode10 & 07;  // get n
            cmp18 (cpu_p->rX[n], GETHI (cpu_p->CY), &cpu_p->cu.IR);
          }
          break;

        case x0 (0111):  // cwl
          // C(Y) :: closed interval [C(A);C(Q)]
          /**
           * The cwl instruction tests the value of C(Y) to determine if it
           * is within the range of values set by C(A) and C(Q). The
           * comparison of C(Y) with C(Q) locates C(Y) with respect to the
           * interval if C(Y) is not contained within the
           interval.
           */
          cmp36wl (cpu_p->rA, cpu_p->CY, cpu_p->rQ, &cpu_p->cu.IR);
          break;

        /// Fixed-Point Miscellaneous

        case x0 (0234):  // szn
          // Set indicators according to C(Y)
          cpu_p->CY &= DMASK;
          SC_I_ZERO (cpu_p->CY == 0);
          SC_I_NEG (cpu_p->CY & SIGN36);
          break;

        case x0 (0214):  // sznc
          // Set indicators according to C(Y)
          cpu_p->CY &= DMASK;
          SC_I_ZERO (cpu_p->CY == 0);
          SC_I_NEG (cpu_p->CY & SIGN36);
          // ... and clear
          cpu_p->CY = 0;
#ifdef TEST_OLIN
          cmpxchg ();
#endif
          break;

        /// BOOLEAN OPERATION INSTRUCTIONS

        /// Boolean And

// Optimized to the top of the loop
//        case x0 (0375):  // ana

// Optimized to the top of the loop
//        case x0 (0377):  //< anaq

        case x0 (0376):  // anq
          // C(Q)i & C(Y)i -> C(Q)i for i = (0, 1, ..., 35)
          cpu_p->rQ = cpu_p->rQ & cpu_p->CY;
          cpu_p->rQ &= DMASK;
          HDBGRegQ ();

          SC_I_ZERO (cpu_p->rQ == 0);
          SC_I_NEG (cpu_p->rQ & SIGN36);
          break;

        case x0 (0355):  // ansa
          // C(A)i & C(Y)i -> C(Y)i for i = (0, 1, ..., 35)
          {
            cpu_p->CY = cpu_p->rA & cpu_p->CY;
            cpu_p->CY &= DMASK;
            HDBGRegA ();

            SC_I_ZERO (cpu_p->CY == 0);
            SC_I_NEG (cpu_p->CY & SIGN36);
          }
#ifdef TEST_OLIN
          cmpxchg ();
#endif
          break;

        case x0 (0356):  // ansq
          // C(Q)i & C(Y)i -> C(Y)i for i = (0, 1, ..., 35)
          {
              cpu_p->CY = cpu_p->rQ & cpu_p->CY;
              cpu_p->CY &= DMASK;

              SC_I_ZERO (cpu_p->CY == 0);
              SC_I_NEG (cpu_p->CY & SIGN36);
          }
#ifdef TEST_OLIN
          cmpxchg ();
#endif
          break;

                         // ansxn
        case x0 (0340):  // ansx0
        case x0 (0341):  // ansx1
        case x0 (0342):  // ansx2
        case x0 (0343):  // ansx3
        case x0 (0344):  // ansx4
        case x0 (0345):  // ansx5
        case x0 (0346):  // ansx6
        case x0 (0347):  // ansx7
          // For n = 0, 1, ..., or 7 as determined by operation code
          // C(Xn)i & C(Y)i -> C(Y)i for i = (0, 1, ..., 17)
          {
            uint32 n = opcode10 & 07;  // get n
            word18 tmp18 = cpu_p->rX[n] & GETHI (cpu_p->CY);
            tmp18 &= MASK18;

            SC_I_ZERO (tmp18 == 0);
            SC_I_NEG (tmp18 & SIGN18);

            SETHI (cpu_p->CY, tmp18);
          }
#ifdef TEST_OLIN
          cmpxchg ();
#endif

          break;

                         // anxn
        case x0 (0360):  // anx0
        case x0 (0361):  // anx1
        case x0 (0362):  // anx2
        case x0 (0363):  // anx3
        case x0 (0364):  // anx4
        case x0 (0365):  // anx5
        case x0 (0366):  // anx6
        case x0 (0367):  // anx7
          // For n = 0, 1, ..., or 7 as determined by operation code
          // C(Xn)i & C(Y)i -> C(Xn)i for i = (0, 1, ..., 17)
          {
              uint32 n = opcode10 & 07;  // get n
              cpu_p->rX[n] &= GETHI (cpu_p->CY);
              cpu_p->rX[n] &= MASK18;
              HDBGRegX (n);

              SC_I_ZERO (cpu_p->rX[n] == 0);
              SC_I_NEG (cpu_p->rX[n] & SIGN18);
          }
          break;

        /// Boolean Or

// Optimized to the top of the loop
//        case x0 (0275):  // ora

        case x0 (0277):  // oraq
          // C(AQ)i | C(Y-pair)i -> C(AQ)i for i = (0, 1, ..., 71)
          {
              word72 tmp72 = YPAIRTO72 (cpu_p->Ypair);
              word72 trAQ = convert_to_word72 (cpu_p->rA, cpu_p->rQ);
#ifdef NEED_128
              trAQ = or_128 (trAQ, tmp72);
              trAQ = and_128 (trAQ, MASK72);

              SC_I_ZERO (iszero_128 (trAQ));
              SC_I_NEG (isnonzero_128 (and_128 (trAQ, SIGN72)));
#else
              trAQ = trAQ | tmp72;
              trAQ &= MASK72;

              SC_I_ZERO (trAQ == 0);
              SC_I_NEG (trAQ & SIGN72);
#endif
              convert_to_word36 (trAQ, &cpu_p->rA, &cpu_p->rQ);
              HDBGRegA ();
              HDBGRegQ ();
          }
          break;

        case x0 (0276):  // orq
          // C(Q)i | C(Y)i -> C(Q)i for i = (0, 1, ..., 35)
          cpu_p->rQ = cpu_p->rQ | cpu_p->CY;
          cpu_p->rQ &= DMASK;
          HDBGRegQ ();

          SC_I_ZERO (cpu_p->rQ == 0);
          SC_I_NEG (cpu_p->rQ & SIGN36);

          break;

        case x0 (0255):  // orsa
          // C(A)i | C(Y)i -> C(Y)i for i = (0, 1, ..., 35)
          cpu_p->CY = cpu_p->rA | cpu_p->CY;
          cpu_p->CY &= DMASK;

          SC_I_ZERO (cpu_p->CY == 0);
          SC_I_NEG (cpu_p->CY & SIGN36);
#ifdef TEST_OLIN
          cmpxchg ();
#endif
          break;

        case x0 (0256):  // orsq
          // C(Q)i | C(Y)i -> C(Y)i for i = (0, 1, ..., 35)

          cpu_p->CY = cpu_p->rQ | cpu_p->CY;
          cpu_p->CY &= DMASK;

          SC_I_ZERO (cpu_p->CY == 0);
          SC_I_NEG (cpu_p->CY & SIGN36);
#ifdef TEST_OLIN
          cmpxchg ();
#endif
          break;

                         // orsxn
        case x0 (0240):  // orsx0
        case x0 (0241):  // orsx1
        case x0 (0242):  // orsx2
        case x0 (0243):  // orsx3
        case x0 (0244):  // orsx4
        case x0 (0245):  // orsx5
        case x0 (0246):  // orsx6
        case x0 (0247):  // orsx7
          // For n = 0, 1, ..., or 7 as determined by operation code
          // C(Xn)i | C(Y)i -> C(Y)i for i = (0, 1, ..., 17)
          {
            uint32 n = opcode10 & 07;  // get n

            word18 tmp18 = cpu_p->rX[n] | GETHI (cpu_p->CY);
            tmp18 &= MASK18;

            SC_I_ZERO (tmp18 == 0);
            SC_I_NEG (tmp18 & SIGN18);

            SETHI (cpu_p->CY, tmp18);
          }
#ifdef TEST_OLIN
          cmpxchg ();
#endif
          break;

                         // orxn
        case x0 (0260):  // orx0
        case x0 (0261):  // orx1
        case x0 (0262):  // orx2
        case x0 (0263):  // orx3
        case x0 (0264):  // orx4
        case x0 (0265):  // orx5
        case x0 (0266):  // orx6
        case x0 (0267):  // orx7
          // For n = 0, 1, ..., or 7 as determined by operation code
          // C(Xn)i | C(Y)i -> C(Xn)i for i = (0, 1, ..., 17)
          {
              uint32 n = opcode10 & 07;  // get n
              cpu_p->rX[n] |= GETHI (cpu_p->CY);
              cpu_p->rX[n] &= MASK18;
              HDBGRegX (n);

              SC_I_ZERO (cpu_p->rX[n] == 0);
              SC_I_NEG (cpu_p->rX[n] & SIGN18);
          }
          break;

        /// Boolean Exclusive Or

        case x0 (0675):  // era
          // C(A)i XOR C(Y)i -> C(A)i for i = (0, 1, ..., 35)
          cpu_p->rA = cpu_p->rA ^ cpu_p->CY;
          cpu_p->rA &= DMASK;
          HDBGRegA ();

          SC_I_ZERO (cpu_p->rA == 0);
          SC_I_NEG (cpu_p->rA & SIGN36);

          break;

// Optimized to the top of the loop
//        case x0 (0677):  // eraq

        case x0 (0676):  // erq
          // C(Q)i XOR C(Y)i -> C(Q)i for i = (0, 1, ..., 35)
          cpu_p->rQ = cpu_p->rQ ^ cpu_p->CY;
          cpu_p->rQ &= DMASK;
          HDBGRegQ ();
          SC_I_ZERO (cpu_p->rQ == 0);
          SC_I_NEG (cpu_p->rQ & SIGN36);
          break;

        case x0 (0655):  // ersa
          // C(A)i XOR C(Y)i -> C(Y)i for i = (0, 1, ..., 35)

          cpu_p->CY = cpu_p->rA ^ cpu_p->CY;
          cpu_p->CY &= DMASK;

          SC_I_ZERO (cpu_p->CY == 0);
          SC_I_NEG (cpu_p->CY & SIGN36);
#ifdef TEST_OLIN
          cmpxchg ();
#endif
          break;

        case x0 (0656):  // ersq
          // C(Q)i XOR C(Y)i -> C(Y)i for i = (0, 1, ..., 35)

          cpu_p->CY = cpu_p->rQ ^ cpu_p->CY;
          cpu_p->CY &= DMASK;

          SC_I_ZERO (cpu_p->CY == 0);
          SC_I_NEG (cpu_p->CY & SIGN36);
#ifdef TEST_OLIN
          cmpxchg ();
#endif

          break;

                          // ersxn
        case x0 (0640):   // ersx0
        case x0 (0641):   // ersx1
        case x0 (0642):   // ersx2
        case x0 (0643):   // ersx3
        case x0 (0644):   // ersx4
        case x0 (0645):   // ersx5
        case x0 (0646):   // ersx6
        case x0 (0647):   // ersx7
          // For n = 0, 1, ..., or 7 as determined by operation code
          // C(Xn)i XOR C(Y)i -> C(Y)i for i = (0, 1, ..., 17)
          {
            uint32 n = opcode10 & 07;  // get n

            word18 tmp18 = cpu_p->rX[n] ^ GETHI (cpu_p->CY);
            tmp18 &= MASK18;

            SC_I_ZERO (tmp18 == 0);
            SC_I_NEG (tmp18 & SIGN18);

            SETHI (cpu_p->CY, tmp18);
          }
#ifdef TEST_OLIN
          cmpxchg ();
#endif
          break;

                         // erxn
        case x0 (0660):  // erx0
        case x0 (0661):  // erx1
        case x0 (0662):  // erx2
        case x0 (0663):  // erx3
        case x0 (0664):  // erx4
        case x0 (0665):  // erx5
        case x0 (0666):  // erx6 !!!! Beware !!!!
        case x0 (0667):  // erx7
          // For n = 0, 1, ..., or 7 as determined by operation code
          // C(Xn)i XOR C(Y)i -> C(Xn)i for i = (0, 1, ..., 17)
          {
            uint32 n = opcode10 & 07;  // get n
            cpu_p->rX[n] ^= GETHI (cpu_p->CY);
            cpu_p->rX[n] &= MASK18;
            HDBGRegX (n);

            SC_I_ZERO (cpu_p->rX[n] == 0);
            SC_I_NEG (cpu_p->rX[n] & SIGN18);
          }
          break;

        /// Boolean Comparative And

// Optimized to the top of the loop
//        case x0 (0315):  // cana

        case x0 (0317):  // canaq
          // C(Z)i = C(AQ)i & C(Y-pair)i for i = (0, 1, ..., 71)
          {
            word72 tmp72 = YPAIRTO72 (cpu_p->Ypair);
            word72 trAQ = convert_to_word72 (cpu_p->rA, cpu_p->rQ);
#ifdef NEED_128
            trAQ = and_128 (trAQ, tmp72);
            trAQ = and_128 (trAQ, MASK72);

            SC_I_ZERO (iszero_128 (trAQ));
            SC_I_NEG (isnonzero_128 (and_128 (trAQ, SIGN72)));
#else
            trAQ = trAQ & tmp72;
            trAQ &= MASK72;

            SC_I_ZERO (trAQ == 0);
            SC_I_NEG (trAQ & SIGN72);
#endif
          }
            break;

        case x0 (0316):  // canq
          // C(Z)i = C(Q)i & C(Y)i for i = (0, 1, ..., 35)
          {
            word36 trZ = cpu_p->rQ & cpu_p->CY;
            trZ &= DMASK;

            SC_I_ZERO (trZ == 0);
            SC_I_NEG (trZ & SIGN36);
          }
          break;

                         // canxn
        case x0 (0300):  // canx0
        case x0 (0301):  // canx1
        case x0 (0302):  // canx2
        case x0 (0303):  // canx3
        case x0 (0304):  // canx4
        case x0 (0305):  // canx5
        case x0 (0306):  // canx6
        case x0 (0307):  // canx7
          // For n = 0, 1, ..., or 7 as determined by operation code
          // C(Z)i = C(Xn)i & C(Y)i for i = (0, 1, ..., 17)
          {
            uint32 n = opcode10 & 07;  // get n
            word18 tmp18 = cpu_p->rX[n] & GETHI (cpu_p->CY);
            tmp18 &= MASK18;
            sim_debug (DBG_TRACEEXT, & cpu_dev,
                       "n %o rX %06o HI %06o tmp %06o\n",
                       n, cpu_p->rX[n], (word18) (GETHI (cpu_p->CY) & MASK18),
                       tmp18);

            SC_I_ZERO (tmp18 == 0);
            SC_I_NEG (tmp18 & SIGN18);
          }
          break;

        /// Boolean Comparative Not

        case x0 (0215):  // cnaa
          // C(Z)i = C(A)i & ~C(Y)i for i = (0, 1, ..., 35)
          {
            word36 trZ = cpu_p->rA & ~cpu_p->CY;
            trZ &= DMASK;

            SC_I_ZERO (trZ == 0);
            SC_I_NEG (trZ & SIGN36);
          }
          break;

        case x0 (0217):  // cnaaq
          // C(Z)i = C (AQ)i & ~C(Y-pair)i for i = (0, 1, ..., 71)
          {
            word72 tmp72 = YPAIRTO72 (cpu_p->Ypair);   //

            word72 trAQ = convert_to_word72 (cpu_p->rA, cpu_p->rQ);
#ifdef NEED_128
            trAQ = and_128 (trAQ, complement_128 (tmp72));
            trAQ = and_128 (trAQ, MASK72);

            SC_I_ZERO (iszero_128 (trAQ));
            SC_I_NEG (isnonzero_128 (and_128 (trAQ, SIGN72)));
#else
            trAQ = trAQ & ~tmp72;
            trAQ &= MASK72;

            SC_I_ZERO (trAQ == 0);
            SC_I_NEG (trAQ & SIGN72);
#endif
          }
          break;

        case x0 (0216):  // cnaq
          // C(Z)i = C(Q)i & ~C(Y)i for i = (0, 1, ..., 35)
          {
            word36 trZ = cpu_p->rQ & ~cpu_p->CY;
            trZ &= DMASK;
            SC_I_ZERO (trZ == 0);
            SC_I_NEG (trZ & SIGN36);
          }
          break;

                         // cnaxn
        case x0 (0200):  // cnax0
        case x0 (0201):  // cnax1
        case x0 (0202):  // cnax2
        case x0 (0203):  // cnax3
        case x0 (0204):  // cnax4
        case x0 (0205):  // cnax5
        case x0 (0206):  // cnax6
        case x0 (0207):  // cnax7
          // C(Z)i = C(Xn)i & ~C(Y)i for i = (0, 1, ..., 17)
          {
            uint32 n = opcode10 & 07;  // get n
            word18 tmp18 = cpu_p->rX[n] & ~GETHI (cpu_p->CY);
            tmp18 &= MASK18;

            SC_I_ZERO (tmp18 == 0);
            SC_I_NEG (tmp18 & SIGN18);
          }
          break;

        /// FLOATING-POINT ARITHMETIC INSTRUCTIONS

        /// Floating-Point Data Movement Load

        case x0 (0433):  // dfld
          // C(Y-pair)0,7 -> C(E)
          // C(Y-pair)8,71 -> C(AQ)0,63
          // 00...0 -> C(AQ)64,71
          // Zero: If C(AQ) = 0, then ON; otherwise OFF
          // Neg: If C(AQ)0 = 1, then ON; otherwise OFF

          CPTUR (cptUseE);
          cpu_p->rE = (cpu_p->Ypair[0] >> 28) & MASK8;

          cpu_p->rA = (cpu_p->Ypair[0] & FLOAT36MASK) << 8;
          cpu_p->rA |= (cpu_p->Ypair[1] >> 28) & MASK8;
          HDBGRegA ();

          cpu_p->rQ = (cpu_p->Ypair[1] & FLOAT36MASK) << 8;
          HDBGRegQ ();

          SC_I_ZERO (cpu_p->rA == 0 && cpu_p->rQ == 0);
          SC_I_NEG (cpu_p->rA & SIGN36);
          break;

// Optimized to the top of the loop
//        case x0 (0431):  // fld

        /// Floating-Point Data Movement Store

        case x0 (0457):  // dfst
          // C(E) -> C(Y-pair)0,7
          // C(AQ)0,63 -> C(Y-pair)8,71

          CPTUR (cptUseE);
          cpu_p->Ypair[0] = ((word36)cpu_p->rE << 28) |
                         ((cpu_p->rA & 0777777777400LLU) >> 8);
          cpu_p->Ypair[1] = ((cpu_p->rA & 0377) << 28) |
                         ((cpu_p->rQ & 0777777777400LLU) >> 8);

          break;

        case x0 (0472):  // dfstr

          dfstr (cpu_p->Ypair);
          break;

        case x0 (0455):  // fst
          // C(E) -> C(Y)0,7
          // C(A)0,27 -> C(Y)8,35
          CPTUR (cptUseE);
          cpu_p->rE &= MASK8;
          cpu_p->rA &= DMASK;
          cpu_p->CY = ((word36)cpu_p->rE << 28) | (((cpu_p->rA >> 8) & 01777777777LL));
          break;

        case x0 (0470):  // fstr
          // The fstr instruction performs a true round and normalization on
          // C(EAQ) as it is stored.

//            frd ();
//
//            // C(E) -> C(Y)0,7
//            // C(A)0,27 -> C(Y)8,35
//            cpu_p->CY = ((word36)cpu_p->rE << 28) |
//                     (((cpu_p->rA >> 8) & 01777777777LL));
//
//            // Zero: If C(Y) = floating point 0, then ON; otherwise OFF
//            //SC_I_ZERO ((cpu_p->CY & 01777777777LL) == 0);
//            bool isZero = cpu_p->rE == -128 && cpu_p->rA == 0;
//            SC_I_ZERO (isZero);
//
//            // Neg: If C(Y)8 = 1, then ON; otherwise OFF
//            //SC_I_NEG (cpu_p->CY & 01000000000LL);
//            SC_I_NEG (cpu_p->rA & SIGN36);
//
//            // Exp Ovr: If exponent is greater than +127, then ON
//            // Exp Undr: If exponent is less than -128, then ON
//            // XXX: not certain how these can occur here ....

          fstr (&cpu_p->CY);

          break;

        /// Floating-Point Addition

        case x0 (0477):  // dfad
          // The dfad instruction may be thought of as a dufa instruction
          // followed by a fno instruction.

          CPTUR (cptUseE);
          dufa (false);
          fno (&cpu_p->rE, &cpu_p->rA, &cpu_p->rQ);
          HDBGRegA ();
          HDBGRegQ ();
          break;

        case x0 (0437):  // dufa
          dufa (false);
          break;

        case x0 (0475):  // fad
          // The fad instruction may be thought of a an ufa instruction
          // followed by a fno instruction.
          // (Heh, heh. We'll see....)

          CPTUR (cptUseE);
          ufa (false);
          fno (&cpu_p->rE, &cpu_p->rA, &cpu_p->rQ);
          HDBGRegA ();
          HDBGRegQ ();

          break;

        case x0 (0435):  // ufa
            // C(EAQ) + C(Y) -> C(EAQ)

          ufa (false);
          break;

        /// Floating-Point Subtraction

        case x0 (0577):  // dfsb
          // The dfsb instruction is identical to the dfad instruction with
          // the exception that the twos complement of the mantissa of the
          // operand from main memory is used.

          CPTUR (cptUseE);
          dufa (true);
          fno (&cpu_p->rE, &cpu_p->rA, &cpu_p->rQ);
          HDBGRegA ();
          HDBGRegQ ();
          break;

        case x0 (0537):  // dufs
          dufa (true);
          break;

        case x0 (0575):  // fsb
          // The fsb instruction may be thought of as an ufs instruction
          // followed by a fno instruction.
          CPTUR (cptUseE);
          ufa (true);
          fno (&cpu_p->rE, &cpu_p->rA, &cpu_p->rQ);
          HDBGRegA ();
          HDBGRegQ ();

          break;

        case x0 (0535):  // ufs
          // C(EAQ) - C(Y) -> C(EAQ)
          ufa (true);
          break;

        /// Floating-Point Multiplication

        case x0 (0463):  // dfmp
          // The dfmp instruction may be thought of as a dufm instruction
          // followed by a fno instruction.

          CPTUR (cptUseE);
          dufm ();
          fno (&cpu_p->rE, &cpu_p->rA, &cpu_p->rQ);
          HDBGRegA ();
          HDBGRegQ ();
          break;

        case x0 (0423):  // dufm

          dufm ();
          break;

        case x0 (0461):  // fmp
          // The fmp instruction may be thought of as a ufm instruction
          // followed by a fno instruction.

          CPTUR (cptUseE);
          ufm ();
          fno (&cpu_p->rE, &cpu_p->rA, &cpu_p->rQ);
          HDBGRegA ();
          HDBGRegQ ();

          break;

        case x0 (0421):  // ufm
          // C(EAQ)* C(Y) -> C(EAQ)
          ufm ();
          break;

        /// Floating-Point Division

        case x0 (0527):  // dfdi

          dfdi ();
          break;

        case x0 (0567):  // dfdv

          dfdv ();
          break;

        case x0 (0525):  // fdi
          // C(Y) / C(EAQ) -> C(EA)

          fdi ();
          break;

        case x0 (0565):  // fdv
          // C(EAQ) /C(Y) -> C(EA)
          // 00...0 -> C(Q)
          fdv ();
          break;

        /// Floating-Point Negation

        case x0 (0513):  // fneg
          // -C(EAQ) normalized -> C(EAQ)
          fneg ();
          break;

        /// Floating-Point Normalize

        case x0 (0573):  // fno
          // The fno instruction normalizes the number in C(EAQ) if C(AQ)
          // != 0 and the overflow indicator is OFF.
          //
          // A normalized floating number is defined as one whose mantissa
          // lies in the interval [0.5,1.0) such that 0.5<= |C(AQ)| <1.0
          // which, in turn, requires that C(AQ)0 != C(AQ)1.list
          //
          // !!!! For personal reasons the following 3 lines of comment must
          // never be removed from this program or any code derived
          // therefrom. HWR 25 Aug 2014
          ///Charles Is the coolest
          ///true story y'all
          //you should get me darksisers 2 for christmas

          CPTUR (cptUseE);
          fno (& cpu_p->rE, & cpu_p->rA, & cpu_p->rQ);
          HDBGRegA ();
          HDBGRegQ ();
          break;

        /// Floating-Point Round

        case x0 (0473):  // dfrd
          // C(EAQ) rounded to 64 bits -> C(EAQ)
          // 0 -> C(AQ)64,71 (See notes in dps8_math.c on dfrd())

          dfrd ();
          break;

        case x0 (0471):  // frd
          // C(EAQ) rounded to 28 bits -> C(EAQ)
          // 0 -> C(AQ)28,71 (See notes in dps8_math.c on frd())

          frd ();
          break;

        /// Floating-Point Compare

        case x0 (0427):  // dfcmg
          // C(E) :: C(Y-pair)0,7
          // | C(AQ)0,63 | :: | C(Y-pair)8,71 |

          dfcmg ();
          break;

        case x0 (0517):  // dfcmp
          // C(E) :: C(Y-pair)0,7
          // C(AQ)0,63 :: C(Y-pair)8,71

          dfcmp ();
          break;

        case x0 (0425):  // fcmg
          // C(E) :: C(Y)0,7
          // | C(AQ)0,27 | :: | C(Y)8,35 |

          fcmg ();
          break;

        case x0 (0515):  // fcmp
          // C(E) :: C(Y)0,7
          // C(AQ)0,27 :: C(Y)8,35

          fcmp ();
          break;

        /// Floating-Point Miscellaneous

        case x0 (0415):  // ade
          // C(E) + C(Y)0,7 -> C(E)
          {
            CPTUR (cptUseE);
            int y = SIGNEXT8_int ((cpu_p->CY >> 28) & 0377);
            int e = SIGNEXT8_int (cpu_p->rE);
            e = e + y;

            cpu_p->rE = e & 0377;
            CLR_I_ZERO;
            CLR_I_NEG;

            if (e > 127)
              {
                SET_I_EOFL;
                if (tstOVFfault (cpu_p))
                  doFault (cpu_p, FAULT_OFL, fst_zero, "ade exp overflow fault");
              }

            if (e < -128)
              {
                SET_I_EUFL;
                if (tstOVFfault (cpu_p))
                  doFault (cpu_p, FAULT_OFL, fst_zero, "ade exp underflow fault");
              }
          }
          break;

        case x0 (0430):  // fszn

          // Zero: If C(Y)8,35 = 0, then ON; otherwise OFF
          // Negative: If C(Y)8 = 1, then ON; otherwise OFF

          SC_I_ZERO ((cpu_p->CY & 001777777777LL) == 0);
          SC_I_NEG (cpu_p->CY & 001000000000LL);

          break;

        case x0 (0411):  // lde
          // C(Y)0,7 -> C(E)

          CPTUR (cptUseE);
          cpu_p->rE = (cpu_p->CY >> 28) & 0377;
          CLR_I_ZERO;
          CLR_I_NEG;

          break;

        case x0 (0456):  // ste
          // C(E) -> C(Y)0,7
          // 00...0 -> C(Y)8,17

          CPTUR (cptUseE);
          //putbits36_18 (& cpu_p->CY, 0, ((word18) (cpu_p->rE & 0377) << 10));
          cpu_p->CY = ((word36) (cpu_p->rE & 0377)) << 28;
          cpu_p->zone = 0777777000000;
          cpu_p->useZone = true;
          break;


        /// TRANSFER INSTRUCTIONS

        case x0 (0713):  // call6

          CPTUR (cptUsePRn + 7);

          do_caf (cpu_p);
          read_tra_op (cpu_p);
          sim_debug (DBG_TRACEEXT, & cpu_dev,
                     "call6 PRR %o PSR %o\n", cpu_p->PPR.PRR, cpu_p->PPR.PSR);

          return CONT_TRA;


        case x0 (0630):  // ret
          {
            // Parity mask: If C(Y)27 = 1, and the processor is in absolute or
            // mask privileged mode, then ON; otherwise OFF. This indicator is
            // not affected in the normal or BAR modes.
            // Not BAR mode: Can be set OFF but not ON by the ret instruction
            // Absolute mode: Can be set OFF but not ON by the ret instruction
            // All oter indicators: If corresponding bit in C(Y) is 1, then ON;
            // otherwise, OFF

            // C(Y)0,17 -> C(PPR.IC)
            // C(Y)18,31 -> C(IR)
            do_caf (cpu_p);
            read_tra_op (cpu_p);

            cpu_p->PPR.IC = GETHI (cpu_p->CY);
            word18 tempIR = GETLO (cpu_p->CY) & 0777770;
            // Assuming 'mask privileged mode' is 'temporary absolute mode'
            if (is_priv_mode (cpu_p)) // abs. or temp. abs. or priv.
              {
                // if abs, copy existing parity mask to tempIR
                // According to ISOLTS pm785, not the case.
                //SCF (TST_I_PMASK, tempIR, I_PMASK);
                // if abs, copy existing I_MIF to tempIR
                SCF (TST_I_MIF, tempIR, I_MIF);
              }
            else
              {
                CLRF (tempIR, I_MIF);
              }
            // can be set OFF but not on
            //  IR   ret   result
            //  off  off   off
            //  off  on    off
            //  on   on    on
            //  on   off   off
            // "If it was on, set it to on"
            //SCF (TST_I_NBAR, tempIR, I_NBAR);
            if (! (TST_I_NBAR && TSTF (tempIR, I_NBAR)))
              {
                CLRF (tempIR, I_NBAR);
              }
            if (! (TST_I_ABS && TSTF (tempIR, I_ABS)))
              {
                CLRF (tempIR, I_ABS);
              }
            

            //sim_debug (DBG_TRACEEXT, & cpu_dev,
            //           "RET NBAR was %d now %d\n",
            //           TST_NBAR ? 1 : 0,
            //           TSTF (tempIR, I_NBAR) ? 1 : 0);
            //sim_debug (DBG_TRACEEXT, & cpu_dev,
            //           "RET ABS  was %d now %d\n",
            //           TST_I_ABS ? 1 : 0,
            //           TSTF (tempIR, I_ABS) ? 1 : 0);
            CPTUR (cptUseIR);
            cpu_p->cu.IR = tempIR;
            return CONT_TRA;
          }

// Optimized to the top of the loop
//        case x0 (0610):  // rtcd

        case x0 (0614):  // teo
          // If exponent overflow indicator ON then
          //  C(TPR.CA) -> C(PPR.IC)
          //  C(TPR.TSR) -> C(PPR.PSR)
          // otherwise, no change to C(PPR)
          if (TST_I_EOFL)
            {
              CLR_I_EOFL;
              do_caf (cpu_p);
              read_tra_op (cpu_p);
              return CONT_TRA;
            }
          break;

        case x0 (0615):  // teu
          // If exponent underflow indicator ON then
          //  C(TPR.CA) -> C(PPR.IC)
          //  C(TPR.TSR) -> C(PPR.PSR)
          if (TST_I_EUFL)
            {
              CLR_I_EUFL;
              do_caf (cpu_p);
              read_tra_op (cpu_p);
              return CONT_TRA;
            }
          break;


// Optimized to the top of the loop
//        case x0 (0604):  // tmi

// Optimized to the top of the loop
//        case x1 (0604):  // tmoz

        case x0 (0602):  // tnc
          // If carry indicator OFF then
          //   C(TPR.CA) -> C(PPR.IC)
          //   C(TPR.TSR) -> C(PPR.PSR)
          if (!TST_I_CARRY)
            {
              do_caf (cpu_p);
              read_tra_op (cpu_p);
              return CONT_TRA;
            }
          break;

// Optimized to the top of the loop
//         case x0 (0601):  // tnz

        case x0 (0617):  // tov
          // If overflow indicator ON then
          //   C(TPR.CA) -> C(PPR.IC)
          //   C(TPR.TSR) -> C(PPR.PSR)
          if (TST_I_OFLOW)
            {
              CLR_I_OFLOW;
              do_caf (cpu_p);
              read_tra_op (cpu_p);
              return CONT_TRA;
            }
          break;

        case x0 (0605):  // tpl
          // If negative indicator OFF, then
          //   C(TPR.CA) -> C(PPR.IC)
          //   C(TPR.TSR) -> C(PPR.PSR)
          if (! (TST_I_NEG))
            {
              do_caf (cpu_p);
              read_tra_op (cpu_p);
              return CONT_TRA;
            }
          break;

// Optimized to the top of the loop
//        case x1 (0605):  // tpnz

// Optimized to the top of the loop
//        case x0 (0710):  // tra


        case x0 (0603):  // trc
          //  If carry indicator ON then
          //    C(TPR.CA) -> C(PPR.IC)
          //    C(TPR.TSR) -> C(PPR.PSR)
          if (TST_I_CARRY)
            {
              do_caf (cpu_p);
              read_tra_op (cpu_p);
              return CONT_TRA;
            }
          break;

        case x1 (0601):  // trtf
            // If truncation indicator OFF then
            //  C(TPR.CA) -> C(PPR.IC)
            //  C(TPR.TSR) -> C(PPR.PSR)
            if (!TST_I_TRUNC)
            {
                do_caf (cpu_p);
                read_tra_op (cpu_p);
                return CONT_TRA;
            }
            break;

        case x1 (0600):  // trtn
            // If truncation indicator ON then
            //  C(TPR.CA) -> C(PPR.IC)
            //  C(TPR.TSR) -> C(PPR.PSR)
            if (TST_I_TRUNC)
            {
                CLR_I_TRUNC;
                do_caf (cpu_p);
                read_tra_op (cpu_p);
                return CONT_TRA;
            }
            break;

// Optimized to the top of the loop
//                         // tspn
//        case x0 (0270):  // tsp0
//        case x0 (0271):  // tsp1
//        case x0 (0272):  // tsp2
//        case x0 (0273):  // tsp3
//        case x0 (0670):  // tsp4
//        case x0 (0671):  // tsp5
//        case x0 (0672):  // tsp6
//        case x0 (0673):  // tsp7

        case x0 (0715):  // tss
          CPTUR (cptUseBAR);
          do_caf (cpu_p);
          if (cpu_p->TPR.CA >= ((word18) cpu_p->BAR.BOUND) << 9)
            {
              doFault (cpu_p, FAULT_ACV, fst_acv15, "TSS boundary violation");
            }
          read_tra_op (cpu_p);
          CLR_I_NBAR;
          return CONT_TRA;

// Optimized to the top of the loop
//                         // tsxn
//        case x0 (0700):  // tsx0
//        case x0 (0701):  // tsx1
//        case x0 (0702):  // tsx2
//        case x0 (0703):  // tsx3
//        case x0 (0704):  // tsx4
//        case x0 (0705):  // tsx5
//        case x0 (0706):  // tsx6
//        case x0 (0707):  // tsx7

        case x0 (0607):  // ttf
          // If tally runout indicator OFF then
          //   C(TPR.CA) -> C(PPR.IC)
          //  C(TPR.TSR) -> C(PPR.PSR)
          // otherwise, no change to C(PPR)
          if (TST_I_TALLY == 0)
            {
              do_caf (cpu_p);
              read_tra_op (cpu_p);
              return CONT_TRA;
            }
          break;

        case x1 (0606):  // ttn
            // If tally runout indicator ON then
            //  C(TPR.CA) -> C(PPR.IC)
            //  C(TPR.TSR) -> C(PPR.PSR)
            // otherwise, no change to C(PPR)
            if (TST_I_TALLY)
            {
                do_caf (cpu_p);
                read_tra_op (cpu_p);
                return CONT_TRA;
            }
            break;

// Optimized to the top of the loop
//        case x0 (0600):  // tze

        /// POINTER REGISTER INSTRUCTIONS

        /// Pointer Register Data Movement Load

                         // easpn

        case x0 (0311):  // easp0
          // C(TPR.CA) -> C(PRn.SNR)
          CPTUR (cptUsePRn + 0);
          cpu_p->PR[0].SNR = cpu_p->TPR.CA & MASK15;
          HDBGRegPR (0);
          break;

        case x1 (0310):  // easp1
          // C(TPR.CA) -> C(PRn.SNR)
          CPTUR (cptUsePRn + 1);
          cpu_p->PR[1].SNR = cpu_p->TPR.CA & MASK15;
          HDBGRegPR (1);
          break;

        case x0 (0313):  // easp2
          // C(TPR.CA) -> C(PRn.SNR)
          CPTUR (cptUsePRn + 2);
          cpu_p->PR[2].SNR = cpu_p->TPR.CA & MASK15;
          HDBGRegPR (2);
          break;

        case x1 (0312):  // easp3
          // C(TPR.CA) -> C(PRn.SNR)
          CPTUR (cptUsePRn + 3);
          cpu_p->PR[3].SNR = cpu_p->TPR.CA & MASK15;
          HDBGRegPR (3);
          break;

        case x0 (0331):  // easp4
          // C(TPR.CA) -> C(PRn.SNR)
          CPTUR (cptUsePRn + 4);
          cpu_p->PR[4].SNR = cpu_p->TPR.CA & MASK15;
          HDBGRegPR (4);
          break;

        case x1 (0330):  // easp5
          // C(TPR.CA) -> C(PRn.SNR)
          CPTUR (cptUsePRn + 5);
          cpu_p->PR[5].SNR = cpu_p->TPR.CA & MASK15;
          HDBGRegPR (5);
          break;

        case x0 (0333):  // easp6
          // C(TPR.CA) -> C(PRn.SNR)
          CPTUR (cptUsePRn + 6);
          cpu_p->PR[6].SNR = cpu_p->TPR.CA & MASK15;
          HDBGRegPR (6);
          break;

        case x1 (0332):  // easp7
          // C(TPR.CA) -> C(PRn.SNR)
          CPTUR (cptUsePRn + 7);
          cpu_p->PR[7].SNR = cpu_p->TPR.CA & MASK15;
          HDBGRegPR (7);
          break;

                         // eawpn

        case x0 (0310):  // eawp0
          // For n = 0, 1, ..., or 7 as determined by operation code
          //  C(TPR.CA) -> C(PRn.WORDNO)
          //  C(TPR.TBR) -> C(PRn.BITNO)
          CPTUR (cptUsePRn + 0);
          cpu_p->PR[0].WORDNO = cpu_p->TPR.CA;
          SET_PR_BITNO (0, cpu_p->TPR.TBR);
          HDBGRegPR (0);
          break;

        case x1 (0311):  // eawp1
          // For n = 0, 1, ..., or 7 as determined by operation code
          //  C(TPR.CA) -> C(PRn.WORDNO)
          //  C(TPR.TBR) -> C(PRn.BITNO)
          CPTUR (cptUsePRn + 1);
          cpu_p->PR[1].WORDNO = cpu_p->TPR.CA;
          SET_PR_BITNO (1, cpu_p->TPR.TBR);
          HDBGRegPR (1);
          break;

        case x0 (0312):  // eawp2
          // For n = 0, 1, ..., or 7 as determined by operation code
          //  C(TPR.CA) -> C(PRn.WORDNO)
          //  C(TPR.TBR) -> C(PRn.BITNO)
          CPTUR (cptUsePRn + 2);
          cpu_p->PR[2].WORDNO = cpu_p->TPR.CA;
          SET_PR_BITNO (2, cpu_p->TPR.TBR);
          HDBGRegPR (2);
          break;

        case x1 (0313):  // eawp3
          // For n = 0, 1, ..., or 7 as determined by operation code
          //  C(TPR.CA) -> C(PRn.WORDNO)
          //  C(TPR.TBR) -> C(PRn.BITNO)
          CPTUR (cptUsePRn + 3);
          cpu_p->PR[3].WORDNO = cpu_p->TPR.CA;
          SET_PR_BITNO (3, cpu_p->TPR.TBR);
          HDBGRegPR (3);
          break;

        case x0 (0330):  // eawp4
          // For n = 0, 1, ..., or 7 as determined by operation code
          //  C(TPR.CA) -> C(PRn.WORDNO)
          //  C(TPR.TBR) -> C(PRn.BITNO)
          CPTUR (cptUsePRn + 4);
          cpu_p->PR[4].WORDNO = cpu_p->TPR.CA;
          SET_PR_BITNO (4, cpu_p->TPR.TBR);
          HDBGRegPR (4);
          break;

        case x1 (0331):  // eawp5
          // For n = 0, 1, ..., or 7 as determined by operation code
          //  C(TPR.CA) -> C(PRn.WORDNO)
          //  C(TPR.TBR) -> C(PRn.BITNO)
          CPTUR (cptUsePRn + 5);
          cpu_p->PR[5].WORDNO = cpu_p->TPR.CA;
          SET_PR_BITNO (5, cpu_p->TPR.TBR);
          HDBGRegPR (5);
          break;

        case x0 (0332):  // eawp6
          // For n = 0, 1, ..., or 7 as determined by operation code
          //  C(TPR.CA) -> C(PRn.WORDNO)
          //  C(TPR.TBR) -> C(PRn.BITNO)
          CPTUR (cptUsePRn + 6);
          cpu_p->PR[6].WORDNO = cpu_p->TPR.CA;
          SET_PR_BITNO (6, cpu_p->TPR.TBR);
          HDBGRegPR (6);
          break;

        case x1 (0333):  // eawp7
          // For n = 0, 1, ..., or 7 as determined by operation code
          //  C(TPR.CA) -> C(PRn.WORDNO)
          //  C(TPR.TBR) -> C(PRn.BITNO)
          CPTUR (cptUsePRn + 7);
          cpu_p->PR[7].WORDNO = cpu_p->TPR.CA;
          SET_PR_BITNO (7, cpu_p->TPR.TBR);
          HDBGRegPR (7);
          break;

// Optimized to the top of the loop
//        case x1 (0350):  // epbp0
//        case x0 (0351):  // epbp1
//        case x1 (0352):  // epbp2
//        case x0 (0353):  // epbp3
//        case x1 (0370):  // epbp4
//        case x0 (0371):  // epbp5
//        case x1 (0372):  // epbp6
//        case x0 (0373):  // epbp7

// Optimized to the top of the switch
//        case x0 (0350):  // epp0
//        case x1 (0351):  // epp1
//        case x0 (0352):  // epp2
//        case x1 (0353):  // epp3
//        case x0 (0374):  // epp4
//        case x1 (0371):  // epp5
//        case x0 (0376):  // epp6
//        case x1 (0373):  // epp7

        case x0 (0173):  // lpri
          // For n = 0, 1, ..., 7
          //  Y-pair = Y-block16 + 2n
          //  Maximum of C(Y-pair)18,20; C(SDW.R1); C(TPR.TRR) -> C(PRn.RNR)
          //  C(Y-pair) 3,17 -> C(PRn.SNR)
          //  C(Y-pair)36,53 -> C(PRn.WORDNO)
          //  C(Y-pair)57,62 -> C(PRn.BITNO)

          for (uint32 n = 0 ; n < 8 ; n ++)
            {
              CPTUR (cptUsePRn + n);
              // Even word of ITS pointer pair
              cpu_p->Ypair[0] = cpu_p->Yblock16[n * 2 + 0];
              // Odd word of ITS pointer pair
              cpu_p->Ypair[1] = cpu_p->Yblock16[n * 2 + 1];

              // RNR from ITS pair
              word3 Crr = (GETLO (cpu_p->Ypair[0]) >> 15) & 07;
              if (get_addr_mode (cpu_p) == APPEND_mode)
                cpu_p->PR[n].RNR = max3 (Crr, cpu_p->SDW->R1, cpu_p->TPR.TRR);
              else
                cpu_p->PR[n].RNR = Crr;
              cpu_p->PR[n].SNR = (cpu_p->Ypair[0] >> 18) & MASK15;
              cpu_p->PR[n].WORDNO = GETHI (cpu_p->Ypair[1]);
              word6 bitno = (GETLO (cpu_p->Ypair[1]) >> 9) & 077;
// According to ISOLTS, loading a 077 into bitno results in 037
// pa851    test-04b    lpri test       bar-100176
// test start 105321   patch 105461   subtest loop point 105442
// s/b 77777737
// was 77777733
              if (bitno == 077)
                bitno = 037;
              SET_PR_BITNO (n, bitno);
              HDBGRegPR (n);
            }

          break;

// Optimized to the top of the loop
//                         // lprpn
//        case x0 (0760):  // lprp0
//        case x0 (0761):  // lprp1
//        case x0 (0762):  // lprp2
//        case x0 (0763):  // lprp3
//        case x0 (0764):  // lprp4
//        case x0 (0765):  // lprp5
//        case x0 (0766):  // lprp6
//        case x0 (0767):  // lprp7

        /// Pointer Register Data Movement Store

// Optimized to the top of the loop
//        case x1 (0250):  // spbp0
//        case x0 (0251):  // spbp1
//        case x1 (0252):  // spbp2
//        case x0 (0253):  // spbp3
//        case x1 (0650):  // spbp4
//        case x0 (0651):  // spbp5
//        case x1 (0652):  // spbp6
//        case x0 (0653):  // spbp7

        case x0 (0254):  // spri
          // For n = 0, 1, ..., 7
          //  Y-pair = Y-block16 + 2n

          //  000 -> C(Y-pair)0,2
          //  C(PRn.SNR) -> C(Y-pair)3,17
          //  C(PRn.RNR) -> C(Y-pair)18,20
          //  00...0 -> C(Y-pair)21,29
          //  (43)8 -> C(Y-pair)30,35

          //  C(PRn.WORDNO) -> C(Y-pair)36,53
          //  000 -> C(Y-pair)54,56
          //  C(PRn.BITNO) -> C(Y-pair)57,62
          //  00...0 -> C(Y-pair)63,71

          for (uint32 n = 0 ; n < 8 ; n++)
            {
              CPTUR (cptUsePRn + n);
              cpu_p->Yblock16[2 * n] = 043;
              cpu_p->Yblock16[2 * n] |= ((word36) cpu_p->PR[n].SNR) << 18;
              cpu_p->Yblock16[2 * n] |= ((word36) cpu_p->PR[n].RNR) << 15;

              cpu_p->Yblock16[2 * n + 1] = (word36) cpu_p->PR[n].WORDNO << 18;
              cpu_p->Yblock16[2 * n + 1] |= (word36) GET_PR_BITNO(n) << 9;
            }

          break;

// Optimized to the top of the loop
//        case x0 (0250):  // spri0
//        case x1 (0251):  // spri1
//        case x0 (0252):  // spri2
//        case x1 (0253):  // spri3
//        case x0 (0650):  // spri4
//        case x1 (0255):  // spri5
//        case x0 (0652):  // spri6
//        case x1 (0257):  // spri7

                         // sprpn
        case x0 (0540):  // sprp0
        case x0 (0541):  // sprp1
        case x0 (0542):  // sprp2
        case x0 (0543):  // sprp3
        case x0 (0544):  // sprp4
        case x0 (0545):  // sprp5
        case x0 (0546):  // sprp6
        case x0 (0547):  // sprp7
          // For n = 0, 1, ..., or 7 as determined by operation code
          //  C(PRn.BITNO) -> C(Y)0,5
          //  C(PRn.SNR)3,14 -> C(Y)6,17
          //  C(PRn.WORDNO) -> C(Y)18,35
          {
            uint32 n = opcode10 & 07;  // get n
            CPTUR (cptUsePRn + n);

            // If C(PRn.SNR)0,2 are nonzero, and C(PRn.SNR) != 11...1, then
            // a store fault (illegal pointer) will occur and C(Y) will not
            // be changed.

            if ((cpu_p->PR[n].SNR & 070000) != 0 && cpu_p->PR[n].SNR != MASK15)
              doFault (cpu_p, FAULT_STR, fst_str_ptr, "sprpn");

            cpu_p->CY  =  ((word36) (GET_PR_BITNO(n) & 077)) << 30;
            // lower 12- of 15-bits
            cpu_p->CY |=  ((word36) (cpu_p->PR[n].SNR & 07777)) << 18;
            cpu_p->CY |=  cpu_p->PR[n].WORDNO & PAMASK;
            cpu_p->CY &= DMASK;    // keep to 36-bits
          }
          break;

        /// Pointer Register Address Arithmetic

                          // adwpn
        case x0 (0050):   // adwp0
        case x0 (0051):   // adwp1
        case x0 (0052):   // adwp2
        case x0 (0053):   // adwp3
          // For n = 0, 1, ..., or 7 as determined by operation code
          //   C(Y)0,17 + C(PRn.WORDNO) -> C(PRn.WORDNO)
          //   00...0 -> C(PRn.BITNO)
          {
              uint32 n = opcode10 & 03;  // get n
              CPTUR (cptUsePRn + n);
              cpu_p->PR[n].WORDNO += GETHI (cpu_p->CY);
              cpu_p->PR[n].WORDNO &= MASK18;
              SET_PR_BITNO (n, 0);
              HDBGRegPR (n);
          }
          break;

        case x0 (0150):   // adwp4
        case x0 (0151):   // adwp5
        case x0 (0152):   // adwp6
        case x0 (0153):   // adwp7
          // For n = 0, 1, ..., or 7 as determined by operation code
          //   C(Y)0,17 + C(PRn.WORDNO) -> C(PRn.WORDNO)
          //   00...0 -> C(PRn.BITNO)
          {
              uint32 n = (opcode10 & MASK3) + 4U;  // get n
              CPTUR (cptUsePRn + n);
              cpu_p->PR[n].WORDNO += GETHI (cpu_p->CY);
              cpu_p->PR[n].WORDNO &= MASK18;
              SET_PR_BITNO (n, 0);
              HDBGRegPR (n);
          }
          break;

        /// Pointer Register Miscellaneous

// Optimized to the top of the loop
//        case x0 (0213):  // epaq

        /// MISCELLANEOUS INSTRUCTIONS

        case x0 (0633):  // rccl
          // 00...0 -> C(AQ)0,19
          // C(calendar clock) -> C(AQ)20,71
          {
// XXX see ticket #23
            // For the rccl instruction, the first 2 or 3 bits of the addr
            // field of the instruction are used to specify which SCU.
            // init_processor.alm systematically steps through the SCUs,
            // using addresses 000000 100000 200000 300000.
#ifdef DPS8M
            uint cpu_port_num = (cpu_p->TPR.CA >> 15) & 03;
#endif
#ifdef L68
            uint cpu_port_num = (cpu_p->TPR.CA >> 15) & 07;
#endif
            if (! get_scu_in_use (current_running_cpu_idx, cpu_port_num))
              {
                sim_warn ("rccl on CPU %u port %d has no SCU; faulting\n",
                          current_running_cpu_idx, cpu_port_num);
                doFault (cpu_p, FAULT_ONC, fst_onc_nem, "(rccl)");
              }
            uint scuUnitIdx = get_scu_idx (current_running_cpu_idx, cpu_port_num);

            t_stat rc = scu_rscr ((uint) scuUnitIdx, current_running_cpu_idx,
                                  040, & cpu_p->rA, & cpu_p->rQ);
            HDBGRegA ();
            HDBGRegQ ();
            if (rc > 0)
              return rc;
#ifndef SPEED
            if_sim_debug (DBG_TRACEEXT, & cpu_dev)
              {
                // Clock at initialization
                // date -d "Tue Jul 22 16:39:38 PDT 1999" +%s
                // 932686778
                uint64 UnixSecs = 932686778;
                uint64 UnixuSecs = UnixSecs * 1000000LL;
                // now determine uSecs since Jan 1, 1901 ...
                uint64 MulticsuSecs = 2177452800000000LL + UnixuSecs;

                // Back into 72 bits
               word72 big = convert_to_word72 (cpu_p->rA, cpu_p->rQ);
#ifdef NEED_128
                // Convert to time since boot
                big = subtract_128 (big, construct_128 (0, MulticsuSecs));
                uint32_t remainder;
                uint128 bigsecs = divide_128_32 (big, 1000000u, & remainder);
                uint64_t uSecs = remainder;
                uint64_t secs = bigsecs.l;
                sim_debug (DBG_TRACEEXT, & cpu_dev,
                           "Clock time since boot %4llu.%06llu seconds\n",
                           secs, uSecs);
#else
                // Convert to time since boot
                big -= MulticsuSecs;
                unsigned long uSecs = big % 1000000u;
                unsigned long secs = (unsigned long) (big / 1000000u);
                sim_debug (DBG_TRACEEXT, & cpu_dev,
                           "Clock time since boot %4lu.%06lu seconds\n",
                           secs, uSecs);
#endif
              }
#endif
          }
          break;

        case x0 (0002):   // drl
          // Causes a fault which fetches and executes, in absolute mode, the
          // instruction pair at main memory location C+(14)8. The value of C
          // is obtained from the FAULT VECTOR switches on the processor
          // configuration panel.

          if (cpu_p->switches.drl_fatal)
            {
              return STOP_STOP;
            }
          doFault (cpu_p, FAULT_DRL, fst_zero, "drl");

        case x0 (0716):  // xec
          cpu_p->cu.xde = 1;
          cpu_p->cu.xdo = 0;
// XXX NB. This used to be done in executeInstruction post-execution
// processing; moving it here means that post-execution code cannot inspect IWB
// to determine what the instruction or it flags were.
          cpu_p->cu.IWB = cpu_p->CY;
          return CONT_XEC;

        case x0 (0717):  // xed
          // The xed instruction itself does not affect any indicator.
          // However, the execution of the instruction pair from C(Y-pair)
          // may affect indicators.
          //
          // The even instruction from C(Y-pair) must not alter
          // C(Y-pair)36,71, and must not be another xed instruction.
          //
          // If the execution of the instruction pair from C(Y-pair) alters
          // C(PPR.IC), then a transfer of control occurs; otherwise, the
          // next instruction to be executed is fetched from C(PPR.IC)+1. If
          // the even instruction from C(Y-pair) alters C(PPR.IC), then the
          // transfer of control is effective immediately and the odd
          // instruction is not executed.
          //
          // To execute an instruction pair having an rpd instruction as the
          // odd instruction, the xed instruction must be located at an odd
          // address. The instruction pair repeated is that instruction pair
          // at C PPR.IC)+1, that is, the instruction pair immediately
          // following the xed instruction. C(PPR.IC) is adjusted during the
          // execution of the repeated instruction pair so the the next
          // instruction fetched for execution is from the first word
          // following the repeated instruction pair.
          //
          // The instruction pair at C(Y-pair) may cause any of the processor
          // defined fault conditions, but only the directed faults (0,1,2,3)
          // and the access violation fault may be restarted successfully by
          // the hardware. Note that the software induced fault tag (1,2,3)
          // faults cannot be properly restarted.
          //
          //  An attempt to execute an EIS multiword instruction causes an
          //  illegal procedure fault.
          //
          //  Attempted repetition with the rpt, rpd, or rpl instructions
          //  causes an illegal procedure fault.

          cpu_p->cu.xde = 1;
          cpu_p->cu.xdo = 1;
// XXX NB. This used to be done in executeInstruction post-execution
// processing; moving it here means that post-execution code cannot inspect IWB
// to determine what the instruction or it flags were.
          cpu_p->cu.IWB = cpu_p->Ypair[0];
          cpu_p->cu.IRODD = cpu_p->Ypair[1];
          return CONT_XEC;

        case x0 (0001):   // mme
#ifdef TESTING
          if (sim_deb_mme_cntdwn > 0)
            sim_deb_mme_cntdwn --;
#endif
          // Causes a fault that fetches and executes, in absolute mode, the
          // instruction pair at main memory location C+4. The value of C is
          // obtained from the FAULT VECTOR switches on the processor
          // configuration panel.
          doFault (cpu_p, FAULT_MME, fst_zero, "Master Mode Entry (mme)");

        case x0 (0004):   // mme2
          // Causes a fault that fetches and executes, in absolute mode, the
          // instruction pair at main memory location C+(52)8. The value of C
          // is obtained from the FAULT VECTOR switches on the processor
          // configuration panel.
          doFault (cpu_p, FAULT_MME2, fst_zero, "Master Mode Entry 2 (mme2)");

        case x0 (0005):   // mme3
          // Causes a fault that fetches and executes, in absolute mode, the
          // instruction pair at main memory location C+(54)8. The value of C
          // is obtained from the FAULT VECTOR switches on the processor
          // configuration panel.
          doFault (cpu_p, FAULT_MME3, fst_zero, "Master Mode Entry 3 (mme3)");

        case x0 (0007):   // mme4
          // Causes a fault that fetches and executes, in absolute mode, the
          // instruction pair at main memory location C+(56)8. The value of C
          // is obtained from the FAULT VECTOR switches on the processor
          // configuration panel.
          doFault (cpu_p, FAULT_MME4, fst_zero, "Master Mode Entry 4 (mme4)");

        case x0 (0011):   // nop
          break;

        case x0 (0012):   // puls1
          break;

        case x0 (0013):   // puls2
          break;

        /// Repeat

        case x0 (0560):  // rpd
          {
            if ((cpu_p->PPR.IC & 1) == 0)
              doFault (cpu_p, FAULT_IPR, fst_ill_proc, "rpd odd");
            cpu_p->cu.delta = i->tag;
            // a:AL39/rpd1
            word1 c = (i->address >> 7) & 1;
            if (c)
              {
                cpu_p->rX[0] = i->address;    // Entire 18 bits
                HDBGRegX (0);
              }
            cpu_p->cu.rd = 1;
            cpu_p->cu.repeat_first = 1;
          }
          break;

        case x0 (0500):  // rpl
          {
            uint c = (i->address >> 7) & 1;
            cpu_p->cu.delta = i->tag;
            if (c)
              {
                cpu_p->rX[0] = i->address;    // Entire 18 bits
                HDBGRegX (0);
              }
            cpu_p->cu.rl = 1;
            cpu_p->cu.repeat_first = 1;
          }
          break;

        case x0 (0520):  // rpt
          {
            uint c = (i->address >> 7) & 1;
            cpu_p->cu.delta = i->tag;
            if (c)
              {
                cpu_p->rX[0] = i->address;    // Entire 18 bits
                HDBGRegX (0);
              }
            cpu_p->cu.rpt = 1;
            cpu_p->cu.repeat_first = 1;
          }
          break;

        /// Ring Alarm Register

        case x1 (0754):  // sra
            // 00...0 -> C(Y)0,32
            // C(RALR) -> C(Y)33,35

            CPTUR (cptUseRALR);
            cpu_p->CY = (word36)cpu_p->rRALR;

            break;

        /// Store Base Address Register

        case x0 (0550):  // sbar
          // C(BAR) -> C(Y) 0,17
          CPTUR (cptUseBAR);
          //SETHI (cpu_p->CY, (cpu_p->BAR.BASE << 9) | cpu_p->BAR.BOUND);
          cpu_p->CY = ((((word36) cpu_p->BAR.BASE) << 9) | cpu_p->BAR.BOUND) << 18;
          cpu_p->zone = 0777777000000;
          cpu_p->useZone = true;
#ifdef TEST_OLIN
          cmpxchg ();
#endif
          break;


        /// Translation

        case x0 (0505):  // bcd
          // Shift C(A) left three positions
          // | C(A) | / C(Y) -> 4-bit quotient
          // C(A) - C(Y) * quotient -> remainder
          // Shift C(Q) left six positions
          // 4-bit quotient -> C(Q)32,35
          // remainder -> C(A)

          {
            word36 tmp1 = cpu_p->rA & SIGN36; // A0
            word36 tmp36 = (cpu_p->rA << 3) & DMASK;
            word36 tmp36q = tmp36 / cpu_p->CY; // this may be more than 4 bits, keep it for remainder calculation
            word36 tmp36r = 0;
            if (!tmp1) {
                tmp36r = tmp36 - tmp36q * cpu_p->CY;
            } else {
                // ISOLTS-745 05i: bcd when rA is negative.
                // Note that this only gets called in the first round of the bcd
                // conversion; the rA sign bit will get shifted out.
                // Looking at the expected results, it appears that a 'borrow'
                // is represented in a residue style notation -- an unborrow
                // result is 0-9 (000 - 011), a borrowed digit as 6-15 (006-017)
                tmp36q += 6;
                tmp36r = tmp36 + tmp36q * cpu_p->CY;
            }

            cpu_p->rQ <<= 6;       // Shift C(Q) left six positions
            cpu_p->rQ &= DMASK;

            //cpu_p->rQ &= (word36) ~017;     // 4-bit quotient -> C(Q)32,35  lo6 bits already zeroed out
            cpu_p->rQ |= (tmp36q & 017);
            HDBGRegQ ();

            cpu_p->rA = tmp36r & DMASK;    // remainder -> C(A)
            HDBGRegA ();

            SC_I_ZERO (cpu_p->rA == 0);  // If C(A) = 0, then ON;
                                            // otherwise OFF
            SC_I_NEG (tmp1);   // If C(A)0 = 1 before execution,
                                            // then ON; otherwise OFF
          }
          break;

        case x0 (0774):  // gtb
          // C(A)0 -> C(A)0
          // C(A)i XOR C(A)i-1 -> C(A)i for i = 1, 2, ..., 35
          {
            word36 tmp = cpu_p->rA & MASK36;
            word36 mask = SIGN36;

            for (int n=1;n<=35;n++) {
                tmp ^= (tmp & mask) >> 1;
                mask >>= 1;
            }
            
            cpu_p->rA = tmp;
            HDBGRegA ();
            
            SC_I_ZERO (cpu_p->rA == 0);  // If C(A) = 0, then ON;
                                      // otherwise OFF
            SC_I_NEG (cpu_p->rA & SIGN36);   // If C(A)0 = 1, then ON; 
                                          // otherwise OFF
          }
          break;

        /// REGISTER LOAD

        case x0 (0230):  // lbar
          // C(Y)0,17 -> C(BAR)
          CPTUR (cptUseBAR);
          // BAR.BASE is upper 9-bits (0-8)
          cpu_p->BAR.BASE = (GETHI (cpu_p->CY) >> 9) & 0777;
          // BAR.BOUND is next lower 9-bits (9-17)
          cpu_p->BAR.BOUND = GETHI (cpu_p->CY) & 0777;
          break;

        /// PRIVILEGED INSTRUCTIONS

        /// Privileged - Register Load

        case x0 (0674):  // lcpr
          // DPS8M interpratation
          switch (i->tag)
            {
              // Extract bits from 'from' under 'mask' shifted to where (where
              // is dps8 '0 is the msbit.

              case 02: // cache mode register
                {
                  //cpu_p->CMR = cpu_p->CY;
                  // cpu_p->CMR.cache_dir_address = <ignored for lcpr>
                  // cpu_p->CMR.par_bit = <ignored for lcpr>
                  // cpu_p->CMR.lev_ful = <ignored for lcpr>

                  CPTUR (cptUseCMR);
                  // a:AL39/cmr2  If either cache enable bit c or d changes
                  // from disable state to enable state, the entire cache is
                  // cleared.
                  uint csh1_on = getbits36_1 (cpu_p->CY, 54 - 36);
                  uint csh2_on = getbits36_1 (cpu_p->CY, 55 - 36);
                  //bool clear = (cpu_p->CMR.csh1_on == 0 && csh1_on != 0) ||
                               //(cpu_p->CMR.csh1_on == 0 && csh1_on != 0);
                  cpu_p->CMR.csh1_on = (word1) csh1_on;
                  cpu_p->CMR.csh2_on = (word1) csh2_on;
                  //if (clear) // a:AL39/cmr2
                    //{
                    //}
#ifdef L68
                  cpu_p->CMR.opnd_on = getbits36_1 (cpu_p->CY, 56 - 36);
#endif
                  cpu_p->CMR.inst_on = getbits36_1 (cpu_p->CY, 57 - 36);
                  cpu_p->CMR.csh_reg = getbits36_1 (cpu_p->CY, 59 - 36);
                  if (cpu_p->CMR.csh_reg)
                    sim_warn ("LCPR set csh_reg\n");
                  // cpu_p->CMR.str_asd = <ignored for lcpr>
                  // cpu_p->CMR.col_ful = <ignored for lcpr>
                  // cpu_p->CMR.rro_AB = getbits36_1 (cpu_p->CY, 18);
#ifdef DPS8M
                  cpu_p->CMR.bypass_cache = getbits36_1 (cpu_p->CY, 68 - 36);
#endif
                  cpu_p->CMR.luf = getbits36_2 (cpu_p->CY, 70 - 36);
                }
                break;

              case 04: // mode register
                {
#if 1
                  CPTUR (cptUseMR);
                  cpu_p->MR.r = cpu_p->CY;
// XXX TEST/NORMAL switch is set to NORMAL
                  putbits36_1 (& cpu_p->MR.r, 32, 0);
// SBZ
                  putbits36_2 (& cpu_p->MR.r, 33, 0);
#ifdef L68
                  cpu_p->MR.FFV = getbits36_15 (cpu_p->CY, 0);
                  cpu_p->MR.OC_TRAP = getbits36_1 (cpu_p->CY, 16);
                  cpu_p->MR.ADR_TRAP = getbits36_1 (cpu_p->CY, 17);
                  cpu_p->MR.OPCODE = getbits36_9 (cpu_p->CY, 18);
                  cpu_p->MR.OPCODEX = getbits36_1 (cpu_p->CY, 27);
#endif
                  cpu_p->MR.sdpap = getbits36_1 (cpu_p->CY, 20);
                  cpu_p->MR.separ = getbits36_1 (cpu_p->CY, 21);
                  cpu_p->MR.hrhlt = getbits36_1 (cpu_p->CY, 28);
#ifdef DPS8M
                  cpu_p->MR.hrxfr = getbits36_1 (cpu_p->CY, 29);
#endif
                  cpu_p->MR.ihr = getbits36_1 (cpu_p->CY, 30);
                  cpu_p->MR.ihrrs = getbits36_1 (cpu_p->CY, 31);
                  cpu_p->MR.emr = getbits36_1 (cpu_p->CY, 35);
#ifdef DPS8M
                  cpu_p->MR.hexfp = getbits36_1 (cpu_p->CY, 33);
#endif
#else
#ifdef L68
                  cpu_p->MR.FFV = getbits36_15 (cpu_p->CY, 0);
                  cpu_p->MR.isolts_tracks = getbits36_1 (cpu_p->CY, 15);
                  cpu_p->MR.OC_TRAP = getbits36_1 (cpu_p->CY, 16);
                  cpu_p->MR.ADR_TRAP = getbits36_1 (cpu_p->CY, 17);
                  cpu_p->MR.hropc = getbits36_1 (cpu_p->CY, 29);
#if 1
                  //if (cpu_p->MR.OC_TRAP)
                  if (cpu_p->MR.OC_TRAP || cpu_p->MR.hropc)
                    {
                      cpu_p->MR.OPCODE = getbits36_10 (cpu_p->CY, 18);
                    }
                  else
#endif
                    {
                      cpu_p->MR.cuolin = getbits36_1 (cpu_p->CY, 18);
                      cpu_p->MR.solin = getbits36_1 (cpu_p->CY, 19);
                      cpu_p->MR.sdpap = getbits36_1 (cpu_p->CY, 20);
                      cpu_p->MR.separ = getbits36_1 (cpu_p->CY, 21);
// tm/vm are only set if the processor maintainence panel PROG switch is on 
#if 1
                      cpu_p->MR.tm = getbits36_2 (cpu_p->CY, 22);
                      cpu_p->MR.vm = getbits36_2 (cpu_p->CY, 24);
                      cpu_p->MR.isolts_tracks2 = getbits36_2 (cpu_p->CY, 26);
#endif
                    }
                  cpu_p->MR.hrhlt = getbits36_1 (cpu_p->CY, 28);
                  // Captured above
                  //cpu_p->MR.hropc = getbits36_1 (cpu_p->CY, 29);
                  cpu_p->MR.ihr = getbits36_1 (cpu_p->CY, 30);
                  cpu_p->MR.ihrrs = getbits36_1 (cpu_p->CY, 31);
                  //cpu_p->MR.mrgctl = getbits36_1 (cpu_p->CY, 32);
                  cpu_p->MR.emr = getbits36_1 (cpu_p->CY, 35);
#endif
#ifdef DPS8M
                  cpu_p->MR.cuolin = getbits36_1 (cpu_p->CY, 18);
                  cpu_p->MR.solin = getbits36_1 (cpu_p->CY, 19);
                  cpu_p->MR.sdpap = getbits36_1 (cpu_p->CY, 20);
                  cpu_p->MR.separ = getbits36_1 (cpu_p->CY, 21);
// tm/vm are only set if the processor maintainence panel PROG switch is on 
#if 1
                  cpu_p->MR.tm = getbits36_2 (cpu_p->CY, 22);
                  cpu_p->MR.vm = getbits36_2 (cpu_p->CY, 24);
                  cpu_p->MR.isolts_tracks2 = getbits36_2 (cpu_p->CY, 26);
#endif
                  cpu_p->MR.hrhlt = getbits36_1 (cpu_p->CY, 28);
                  cpu_p->MR.hrxfr = getbits36_1 (cpu_p->CY, 29);
                  cpu_p->MR.ihr = getbits36_1 (cpu_p->CY, 30);
                  cpu_p->MR.ihrrs = getbits36_1 (cpu_p->CY, 31);
                  //cpu_p->MR.mrgctl = getbits36_1 (cpu_p->CY, 32);
                  cpu_p->MR.hexfp = getbits36_1 (cpu_p->CY, 33);
                  cpu_p->MR.emr = getbits36_1 (cpu_p->CY, 35);
#endif
#endif

                  // Stop HR Strobe on HR Counter Overflow. (Setting bit 28
                  // shall cause the HR counter to be reset to zero.)
                  // CAC: It is unclear if bit 28 is edge or level 
                  // triggered; assuming level for simplicity.
                  if (cpu_p->MR.hrhlt)
                    {
                      for (uint hset = 0; hset < N_HIST_SETS; hset ++)
                         cpu_p->history_cyclic[hset] = 0;
                    }

#if 0 
                  if (cpu_p->MR.sdpap)
                    {
                      sim_warn ("LCPR set SDPAP\n");
                    }

                  if (cpu_p->MR.separ)
                    {
                      sim_warn ("LCPR set SEPAR\n");
                    }
#endif
                }
                break;

              case 03: // 0's -> history
                {
                  for (uint i = 0; i < N_HIST_SETS; i ++)
                    add_history_force (cpu_p, i, 0, 0);
// XXX ISOLTS pm700 test-01n 
// The test clears the history registers but with ihr & emr set, causing
// the registers to fill with alternating 0's and lcpr instructions.
// Set flag to prevent the LCPR from being recorded.
                    //cpu_p->MR.ihr = 0;
                    cpu_p->skip_cu_hist = true;
                     
                }
                break;

              case 07: // 1's -> history
                {
                  for (uint i = 0; i < N_HIST_SETS; i ++)
                    add_history_force (cpu_p, i, MASK36, MASK36);
// XXX ISOLTS pm700 test-01n 
// The test clears the history registers but with ihr & emr set, causing
// the registers to fill with alternating 0's and lcpr instructions.
// Set flag to prevent the LCPR from being recorded.
                    //cpu_p->MR.ihr = 0;
                    cpu_p->skip_cu_hist = true;
                }
                break;

              default:
                doFault (cpu_p, FAULT_IPR,
                         fst_ill_mod,
                         "lcpr tag invalid");

            }
            break;

        case x0 (0232):  // ldbr
          do_ldbr (cpu_p, cpu_p->Ypair);
          break;

        case x0 (0637):  // ldt
          CPTUR (cptUseTR);
          cpu_p->rTR = (cpu_p->CY >> 9) & MASK27;
          cpu_p->rTRticks = 0;
#if ISOLTS
          cpu_p->shadowTR = cpu_p->TR0 = cpu_p->rTR;
          cpu_p->rTRlsb = 0;
#endif
          sim_debug (DBG_TRACEEXT, & cpu_dev, "ldt TR %d (%o)\n",
                     cpu_p->rTR, cpu_p->rTR);
#ifdef LOOPTRC
elapsedtime ();
 sim_printf (" ldt %d  PSR:IC %05o:%06o\r\n", cpu_p->rTR, cpu_p->PPR.PSR, cpu_p->PPR.IC);
#endif
          // Undocumented feature. return to bce has been observed to
          // experience TRO while masked, setting the TR to -1, and
          // experiencing an unexpected TRo interrupt when unmasking.
          // Reset any pending TRO fault when the TR is loaded.
          clearTROFault (cpu_p);
          break;

        case x1 (0257):  // lptp
#ifdef DPS8M
          break;
#endif
#ifdef L68
          {
            // For i = 0, 1, ..., 15
            //   m = C(PTWAM(i).USE)
            //   C(Y-block16+m)0,14 -> C(PTWAM(m).POINTER)
            //   C(Y-block16+m)15,26 -> C(PTWAM(m).PAGE)
            //   C(Y-block16+m)27 -> C(PTWAM(m).F)

#ifdef WAM
            for (uint i = 0; i < 16; i ++)
              {
                word4 m = cpu_p->PTWAM[i].USE;
                cpu_p->PTWAM[m].POINTER = getbits36_15 (cpu_p->Yblock16[i],  0);
                cpu_p->PTWAM[m].PAGENO =  getbits36_12 (cpu_p->Yblock16[i], 15);
                cpu_p->PTWAM[m].FE =      getbits36_1  (cpu_p->Yblock16[i], 27);
              }
#endif
          }
          break;
#endif

        case x1 (0173):  // lptr
#ifdef DPS8M
          break;
#endif
#ifdef L68
          {
            // For i = 0, 1, ..., 15
            //   m = C(PTWAM(i).USE)
            //   C(Y-block16+m)0,17 -> C(PTWAM(m).ADDR)
            //   C(Y-block16+m)29 -> C(PTWAM(m).M)
#ifdef WAM
            for (uint i = 0; i < 16; i ++)
              {
                word4 m = cpu_p->PTWAM[i].USE;
                cpu_p->PTWAM[m].ADDR = getbits36_18 (cpu_p->Yblock16[i],  0);
                cpu_p->PTWAM[m].M =    getbits36_1  (cpu_p->Yblock16[i], 29);
              }
#endif
          }
          break;
#endif

        case x1 (0774):  // lra
            CPTUR (cptUseRALR);
            cpu_p->rRALR = cpu_p->CY & MASK3;
            sim_debug (DBG_TRACEEXT, & cpu_dev, "RALR set to %o\n", cpu_p->rRALR);
#ifdef LOOPTRC
{
void elapsedtime (void);
elapsedtime ();
 sim_printf (" RALR set to %o  PSR:IC %05o:%06o\r\n", cpu_p->rRALR, cpu_p->PPR.PSR, cpu_p->PPR.IC);
}
#endif
            break;

        case x0 (0257):  // lsdp
#ifdef DPS8M
          break;
#endif
#ifdef L68
          {
            // For i = 0, 1, ..., 15
            //   m = C(SDWAM(i).USE)
            //   C(Y-block16+m)0,14 -> C(SDWAM(m).POINTER)
            //   C(Y-block16+m)27 -> C(SDWAM(m).F) Note: typo in AL39, P(17) should be F(27)
#ifdef WAM
            for (uint i = 0; i < 16; i ++)
              {
                word4 m = cpu_p->SDWAM[i].USE;
                cpu_p->SDWAM[m].POINTER = getbits36_15 (cpu_p->Yblock16[i],  0);
                cpu_p->SDWAM[m].FE =      getbits36_1  (cpu_p->Yblock16[i], 27);
              }
#endif
          }
          break;
#endif

        case x1 (0232):  // lsdr
#ifdef DPS8M
          break;
#endif
#ifdef L68
          {
            // For i = 0, 1, ..., 15
            //   m = C(SDWAM(i).USE)
            //   C(Y-block32+2m)0,23 -> C(SDWAM(m).ADDR)
            //   C(Y-block32+2m)24,32 -> C(SDWAM(m).R1, R2, R3)
            //   C(Y-block32+2m)37,50 -> C(SDWAM(m).BOUND)
            //   C(Y-block32+2m)51,57 -> C(SDWAM(m).R, E, W, P, U, G, C) Note: typo in AL39, 52 should be 51
            //   C(Y-block32+2m)58,71 -> C(SDWAM(m).CL)
#ifdef WAM
            for (uint i = 0; i < 16; i ++)
              {
                word4 m = cpu_p->SDWAM[i].USE;
                uint j = (uint)m * 2;
                cpu_p->SDWAM[m].ADDR =    getbits36_24 (cpu_p->Yblock32[j],  0);
                cpu_p->SDWAM[m].R1 =      getbits36_3  (cpu_p->Yblock32[j], 24);
                cpu_p->SDWAM[m].R2 =      getbits36_3  (cpu_p->Yblock32[j], 27);
                cpu_p->SDWAM[m].R3 =      getbits36_3  (cpu_p->Yblock32[j], 30);

                cpu_p->SDWAM[m].BOUND =   getbits36_14 (cpu_p->Yblock32[j + 1], 37 - 36);
                cpu_p->SDWAM[m].R =       getbits36_1  (cpu_p->Yblock32[j + 1], 51 - 36);
                cpu_p->SDWAM[m].E =       getbits36_1  (cpu_p->Yblock32[j + 1], 52 - 36);
                cpu_p->SDWAM[m].W =       getbits36_1  (cpu_p->Yblock32[j + 1], 53 - 36);
                cpu_p->SDWAM[m].P =       getbits36_1  (cpu_p->Yblock32[j + 1], 54 - 36);
                cpu_p->SDWAM[m].U =       getbits36_1  (cpu_p->Yblock32[j + 1], 55 - 36);
                cpu_p->SDWAM[m].G =       getbits36_1  (cpu_p->Yblock32[j + 1], 56 - 36);
                cpu_p->SDWAM[m].C =       getbits36_1  (cpu_p->Yblock32[j + 1], 57 - 36);
                cpu_p->SDWAM[m].EB =      getbits36_14 (cpu_p->Yblock32[j + 1], 58 - 36);
              }
#endif
          }
          break;
#endif

        case x0 (0613):  // rcu
          doRCU (cpu_p); // never returns

        /// Privileged - Register Store

        case x0 (0452):  // scpr
          {
            uint tag = (i->tag) & MASK6;
            switch (tag)
              {
                case 000: // C(APU history register#1) -> C(Y-pair)
                  {
                    cpu_p->Ypair[0] =
                      cpu_p->history[APU_HIST_REG]
                                 [cpu_p->history_cyclic[APU_HIST_REG]][0];
                    cpu_p->Ypair[1] =
                      cpu_p->history[APU_HIST_REG]
                                 [cpu_p->history_cyclic[APU_HIST_REG]][1];
                    cpu_p->history_cyclic[APU_HIST_REG] =
                      (cpu_p->history_cyclic[APU_HIST_REG] + 1) % N_HIST_SIZE;
                  }
                  break;

                case 001: // C(fault register) -> C(Y-pair)0,35
                          // 00...0 -> C(Y-pair)36,71
                  {
                    CPTUR (cptUseFR);
                    cpu_p->Ypair[0] = cpu_p->faultRegister[0];
                    cpu_p->Ypair[1] = cpu_p->faultRegister[1];
                    cpu_p->faultRegister[0] = 0;
                    cpu_p->faultRegister[1] = 0;
                  }
                  break;

                case 006: // C(mode register) -> C(Y-pair)0,35
                          // C(cache mode register) -> C(Y-pair)36,72
                  {
                    CPTUR (cptUseMR);
                    cpu_p->Ypair[0] = cpu_p->MR.r;
                    putbits36_1 (& cpu_p->Ypair[0], 20, cpu_p->MR.sdpap);
                    putbits36_1 (& cpu_p->Ypair[0], 21, cpu_p->MR.separ);
                    putbits36_1 (& cpu_p->Ypair[0], 30, cpu_p->MR.ihr);
#ifdef DPS8M
                    putbits36_1 (& cpu_p->Ypair[0], 33, cpu_p->MR.hexfp);
#endif
#if 0
                    cpu_p->Ypair[0] = 0;
#ifdef L68
                    putbits36_15 (& cpu_p->Ypair[0], 0, cpu_p->MR.FFV);
                    putbits36_1 (& cpu_p->Ypair[0], 15, cpu_p->MR.isolts_tracks);
                    putbits36_1 (& cpu_p->Ypair[0], 16, cpu_p->MR.OC_TRAP);
                    putbits36_1 (& cpu_p->Ypair[0], 17, cpu_p->MR.ADR_TRAP);
#if 1
                    if (cpu_p->MR.OC_TRAP || cpu_p->MR.hropc)
                      {
                        putbits36_10 (& cpu_p->Ypair[0], 18, cpu_p->MR.OPCODE);
                      }
                    else
#endif
                      {
                        putbits36_1 (& cpu_p->Ypair[0], 18, cpu_p->MR.cuolin);
                        putbits36_1 (& cpu_p->Ypair[0], 19, cpu_p->MR.solin);
                        putbits36_1 (& cpu_p->Ypair[0], 20, cpu_p->MR.sdpap);
                        putbits36_1 (& cpu_p->Ypair[0], 21, cpu_p->MR.separ);
// tm/vm are only set if the processor maintainence panel PROG switch is on 
#if 1
                        putbits36_2 (& cpu_p->Ypair[0], 22, cpu_p->MR.tm);
                        putbits36_2 (& cpu_p->Ypair[0], 24, cpu_p->MR.vm);
#else
                        putbits36_2 (& cpu_p->Ypair[0], 22, 01llu);
                        putbits36_2 (& cpu_p->Ypair[0], 24, 01llu);
#endif
                      }
#endif
#ifdef DPS8M
                    putbits36_1 (& cpu_p->Ypair[0], 18, cpu_p->MR.cuolin);
                    putbits36_1 (& cpu_p->Ypair[0], 19, cpu_p->MR.solin);
                    putbits36_1 (& cpu_p->Ypair[0], 20, cpu_p->MR.sdpap);
                    putbits36_1 (& cpu_p->Ypair[0], 21, cpu_p->MR.separ);
#endif
// tm/vm are only set if the processor maintainence panel PROG switch is on 
#if 1
                    putbits36_2 (& cpu_p->Ypair[0], 22, cpu_p->MR.tm);
                    putbits36_2 (& cpu_p->Ypair[0], 24, cpu_p->MR.vm);
                    putbits36_2 (& cpu_p->Ypair[0], 26, cpu_p->MR.isolts_tracks2);
#else
                    putbits36_2 (& cpu_p->Ypair[0], 22, 01llu);
                    putbits36_2 (& cpu_p->Ypair[0], 24, 01llu);
                    putbits36_2 (& cpu_p->Ypair[0], 26, 03llu);
#endif
                    putbits36_1 (& cpu_p->Ypair[0], 28, cpu_p->MR.hrhlt);
#ifdef DPS8M
                    putbits36_1 (& cpu_p->Ypair[0], 29, cpu_p->MR.hrxfr);
#endif
#ifdef L68
                    putbits36_1 (& cpu_p->Ypair[0], 29, cpu_p->MR.hropc);
#endif
                    putbits36_1 (& cpu_p->Ypair[0], 30, cpu_p->MR.ihr);
                    putbits36_1 (& cpu_p->Ypair[0], 31, cpu_p->MR.ihrrs);
                    //putbits36_1 (& cpu_p->Ypair[0], 32, cpu_p->MR.mrgctl);
#ifdef DPS8M
                    putbits36_1 (& cpu_p->Ypair[0], 33, cpu_p->MR.hexfp);
#endif
                    putbits36_1 (& cpu_p->Ypair[0], 35, cpu_p->MR.emr);
#endif
                    CPTUR (cptUseCMR);
                    cpu_p->Ypair[1] = 0;
                    putbits36_15 (& cpu_p->Ypair[1], 36 - 36,
                                  cpu_p->CMR.cache_dir_address);
                    putbits36_1 (& cpu_p->Ypair[1], 51 - 36, cpu_p->CMR.par_bit);
                    putbits36_1 (& cpu_p->Ypair[1], 52 - 36, cpu_p->CMR.lev_ful);
                    putbits36_1 (& cpu_p->Ypair[1], 54 - 36, cpu_p->CMR.csh1_on);
                    putbits36_1 (& cpu_p->Ypair[1], 55 - 36, cpu_p->CMR.csh2_on);
#ifdef L68
                    putbits36_1 (& cpu_p->Ypair[1], 56 - 36, cpu_p->CMR.opnd_on);
#endif
                    putbits36_1 (& cpu_p->Ypair[1], 57 - 36, cpu_p->CMR.inst_on);
                    putbits36_1 (& cpu_p->Ypair[1], 59 - 36, cpu_p->CMR.csh_reg);
                    putbits36_1 (& cpu_p->Ypair[1], 60 - 36, cpu_p->CMR.str_asd);
                    putbits36_1 (& cpu_p->Ypair[1], 61 - 36, cpu_p->CMR.col_ful);
                    putbits36_2 (& cpu_p->Ypair[1], 62 - 36, cpu_p->CMR.rro_AB);
#ifdef DPS8M
                    putbits36_1 (& cpu_p->Ypair[1], 68 - 36, 
                                 cpu_p->CMR.bypass_cache);
#endif
                    putbits36_2 (& cpu_p->Ypair[1], 70 - 36, cpu_p->CMR.luf);
                  }
                  break;

                case 010: // C(APU history register#2) -> C(Y-pair)
                  {
#ifdef DPS8M
                    cpu_p->Ypair[0] =
                      cpu_p->history[EAPU_HIST_REG]
                                 [cpu_p->history_cyclic[EAPU_HIST_REG]][0];
                    cpu_p->Ypair[1] =
                      cpu_p->history[EAPU_HIST_REG]
                                 [cpu_p->history_cyclic[EAPU_HIST_REG]][1];
                    cpu_p->history_cyclic[EAPU_HIST_REG] =
                      (cpu_p->history_cyclic[EAPU_HIST_REG] + 1) % N_HIST_SIZE;
#endif
#ifdef L68
                    cpu_p->Ypair[0] =
                      cpu_p->history[DU_HIST_REG]
                                 [cpu_p->history_cyclic[DU_HIST_REG]][0];
                    cpu_p->Ypair[1] =
                      cpu_p->history[DU_HIST_REG]
                                 [cpu_p->history_cyclic[DU_HIST_REG]][1];
                    cpu_p->history_cyclic[DU_HIST_REG] =
                      (cpu_p->history_cyclic[DU_HIST_REG] + 1) % N_HIST_SIZE;
#endif
                  }
                  break;

                case 020: // C(CU history register) -> C(Y-pair)
                  {
                    cpu_p->Ypair[0] =
                      cpu_p->history[CU_HIST_REG]
                                 [cpu_p->history_cyclic[CU_HIST_REG]][0];
                    cpu_p->Ypair[1] =
                      cpu_p->history[CU_HIST_REG]
                                 [cpu_p->history_cyclic[CU_HIST_REG]][1];
                    cpu_p->history_cyclic[CU_HIST_REG] =
                      (cpu_p->history_cyclic[CU_HIST_REG] + 1) % N_HIST_SIZE;
                  }
                  break;

                case 040: // C(OU/DU history register) -> C(Y-pair)
                  {
#ifdef DPS8M
                    cpu_p->Ypair[0] =
                      cpu_p->history[DU_OU_HIST_REG]
                                 [cpu_p->history_cyclic[DU_OU_HIST_REG]][0];
                    cpu_p->Ypair[1] = 
                     cpu_p->history[DU_OU_HIST_REG]
                                 [cpu_p->history_cyclic[DU_OU_HIST_REG]][1];
                    cpu_p->history_cyclic[DU_OU_HIST_REG] =
                      (cpu_p->history_cyclic[DU_OU_HIST_REG] + 1) % N_HIST_SIZE;
#endif
#ifdef L68
                    cpu_p->Ypair[0] =
                      cpu_p->history[OU_HIST_REG]
                                 [cpu_p->history_cyclic[OU_HIST_REG]][0];
                    cpu_p->Ypair[1] = 
                      cpu_p->history[OU_HIST_REG]
                                 [cpu_p->history_cyclic[OU_HIST_REG]][1];
                    cpu_p->history_cyclic[OU_HIST_REG] =
                      (cpu_p->history_cyclic[OU_HIST_REG] + 1) % N_HIST_SIZE;
#endif
                  }
                  break;

                default:
                  {
                    doFault (cpu_p, FAULT_IPR,
                             fst_ill_mod,
                             "SCPR Illegal register select value");
                  }
              }
          }
          break;

        case x0 (0657):  // scu
          // AL-39 defines the behaivor of SCU during fault/interrupt
          // processing, but not otherwise.
          // The T&D tape uses SCU during normal processing, and apparently
          // expects the current CU state to be saved.

          if (cpu_p->cycle == EXEC_cycle)
            {
              // T&D behavior

              // An 'Add Delta' addressing mode will alter the TALLY bit;
              // restore it.
              //SC_I_TALLY (cpu_p->currentInstruction.stiTally == 0);

              scu2words (cpu_p, cpu_p->Yblock8);
            }
          else
            {
              // AL-39 behavior
              for (int j = 0; j < 8; j ++)
                cpu_p->Yblock8[j] = cpu_p->scu_data[j];
            }
          break;

        case x0 (0154):  // sdbr
          {
            CPTUR (cptUseDSBR);
            // C(DSBR.ADDR) -> C(Y-pair) 0,23
            // 00...0 -> C(Y-pair) 24,36
            cpu_p->Ypair[0] = ((word36) (cpu_p->DSBR.ADDR & PAMASK)) << (35 - 23); 

            // C(DSBR.BOUND) -> C(Y-pair) 37,50
            // 0000 -> C(Y-pair) 51,54
            // C(DSBR.U) -> C(Y-pair) 55
            // 000 -> C(Y-pair) 56,59
            // C(DSBR.STACK) -> C(Y-pair) 60,71
            cpu_p->Ypair[1] = ((word36) (cpu_p->DSBR.BND & 037777)) << (71 - 50) |
                           ((word36) (cpu_p->DSBR.U & 1)) << (71 - 55) |
                           ((word36) (cpu_p->DSBR.STACK & 07777)) << (71 - 71);
          }
          break;

        case x1 (0557):  // sptp
          {
// XXX AL39 The associative memory is ignored (forced to "no match") during address
// preparation.
            // Level j is selected by C(TPR.CA)12,13
#ifdef DPS8M
            uint level = (cpu_p->TPR.CA >> 4) & 03;
#endif
#ifdef L68
            uint level = 0;
#endif
#ifdef WAM
            uint toffset = level * 16;
#endif
            for (uint j = 0; j < 16; j ++)
              {
                cpu_p->Yblock16[j] = 0;
#ifdef WAM
                putbits36_15 (& cpu_p->Yblock16[j],  0,
                           cpu_p->PTWAM[toffset + j].POINTER);
#ifdef DPS8M
                putbits36_12 (& cpu_p->Yblock16[j], 15,
                           cpu_p->PTWAM[toffset + j].PAGENO & 07760);

                uint parity = 0;
                if (cpu_p->PTWAM[toffset + j].FE)
                {
                    // calculate parity
                    // 58009997-040 p.101,111
                    parity = ((uint) cpu_p->PTWAM[toffset + j].POINTER << 4) | (cpu_p->PTWAM[toffset + j].PAGENO >> 8);
                    parity = parity ^ (parity >>16);
                    parity = parity ^ (parity >> 8);
                    parity = parity ^ (parity >> 4);
                    parity = ~ (0x6996u >> (parity & 0xf)); 
                }
                putbits36_1 (& cpu_p->Yblock16[j], 23, (word1) (parity & 1));
#endif
#ifdef L68
                putbits36_12 (& cpu_p->Yblock16[j], 15,
                           cpu_p->PTWAM[toffset + j].PAGENO);
#endif
                putbits36_1 (& cpu_p->Yblock16[j], 27, 
                           cpu_p->PTWAM[toffset + j].FE);
#ifdef DPS8M
                putbits36_6 (& cpu_p->Yblock16[j], 30,
                           cpu_p->PTWAM[toffset + j].USE);
#endif
#ifdef L68
                putbits36_4 (& cpu_p->Yblock16[j], 32,
                           cpu_p->PTWAM[toffset + j].USE);
#endif

#endif
              }
#ifndef WAM
            if (level == 0)
              {
                putbits36 (& cpu_p->Yblock16[0],  0, 15,
                           cpu_p->PTW0.POINTER);
#ifdef DPS8M
                putbits36 (& cpu_p->Yblock16[0], 15, 12,
                           cpu_p->PTW0.PAGENO & 07760);
#endif
#ifdef L68
                putbits36 (& cpu_p->Yblock16[0], 15, 12,
                           cpu_p->PTW0.PAGENO);
#endif
                putbits36 (& cpu_p->Yblock16[0], 27,  1,
                           cpu_p->PTW0.FE);
#ifdef DPS8M
                putbits36 (& cpu_p->Yblock16[0], 30,  6,
                           cpu_p->PTW0.USE);
#endif
#ifdef L68
                putbits36 (& cpu_p->Yblock16[0], 32,  4,
                           cpu_p->PTW0.USE);
#endif
              }
#endif
          }
          break;

        case x1 (0154):  // sptr
          {
// XXX The associative memory is ignored (forced to "no match") during address
// preparation.

            // Level j is selected by C(TPR.CA)12,13
#ifdef DPS8M
            uint level = (cpu_p->TPR.CA >> 4) & 03;
#endif
#ifdef L68
            uint level = 0;
#endif
#ifdef WAM
            uint toffset = level * 16;
#endif
            for (uint j = 0; j < 16; j ++)
              {
                cpu_p->Yblock16[j] = 0;
#ifdef WAM
#ifdef DPS8M
                putbits36_18 (& cpu_p->Yblock16[j], 0,
                              cpu_p->PTWAM[toffset + j].ADDR & 0777760);
#endif
#ifdef L68
                putbits36_18 (& cpu_p->Yblock16[j], 0,
                              cpu_p->PTWAM[toffset + j].ADDR);
#endif
                putbits36_1 (& cpu_p->Yblock16[j], 29,
                             cpu_p->PTWAM[toffset + j].M);
#endif
              }
#ifndef WAM
            if (level == 0)
              {
#ifdef DPS8M
                putbits36 (& cpu_p->Yblock16[0], 0, 13, cpu_p->PTW0.ADDR & 0777760);
#endif
#ifdef L68
                putbits36 (& cpu_p->Yblock16[0], 0, 13, cpu_p->PTW0.ADDR);
#endif
                putbits36_1 (& cpu_p->Yblock16[0], 29, cpu_p->PTW0.M);
              }
#endif
          }
          break;

        case x0 (0557):  // ssdp
          {
            // XXX AL39: The associative memory is ignored (forced to "no match")
            // during address preparation.
            // Level j is selected by C(TPR.CA)12,13
#ifdef DPS8M
            uint level = (cpu_p->TPR.CA >> 4) & 03;
#endif
#ifdef L68
            uint level = 0;
#endif
#ifdef WAM
            uint toffset = level * 16;
#endif
            for (uint j = 0; j < 16; j ++)
              {
                cpu_p->Yblock16[j] = 0;
#ifdef WAM
                putbits36_15 (& cpu_p->Yblock16[j], 0,
                           cpu_p->SDWAM[toffset + j].POINTER);
                putbits36_1 (& cpu_p->Yblock16[j], 27,
                           cpu_p->SDWAM[toffset + j].FE);
#ifdef DPS8M
                uint parity = 0;
                if (cpu_p->SDWAM[toffset + j].FE)
                {
                    // calculate parity
                    // 58009997-040 p.112
                    parity = cpu_p->SDWAM[toffset + j].POINTER >> 4;
                    //parity = parity ^ (parity >>16);
                    parity = parity ^ (parity >> 8);
                    parity = parity ^ (parity >> 4);
                    parity = ~ (0x6996u >> (parity & 0xf)); 
                }
                putbits36_1 (& cpu_p->Yblock16[j], 15, (word1) (parity & 1));

                putbits36_6 (& cpu_p->Yblock16[j], 30,
                           cpu_p->SDWAM[toffset + j].USE);
#endif
#ifdef L68
                putbits36_4 (& cpu_p->Yblock16[j], 32,
                           cpu_p->SDWAM[toffset + j].USE);
#endif
#endif
              }
#ifndef WAM
            if (level == 0)
              {
                putbits36 (& cpu_p->Yblock16[0], 0, 15,
                           cpu_p->SDW0.POINTER);
                putbits36 (& cpu_p->Yblock16[0], 27, 1,
                           cpu_p->SDW0.FE);
#ifdef DPS8M
                putbits36 (& cpu_p->Yblock16[0], 30, 6,
                           cpu_p->SDW0.USE);
#endif
#ifdef L68
                putbits36 (& cpu_p->Yblock16[0], 32, 4,
                           cpu_p->SDW0.USE);
#endif
              }
#endif
          }
          break;

        case x1 (0254):  // ssdr
          {
// XXX AL39: The associative memory is ignored (forced to "no match") during
// address preparation.

            // Level j is selected by C(TPR.CA)11,12
            // Note: not bits 12,13. This is due to operand being Yblock32
#ifdef DPS8M
            uint level = (cpu_p->TPR.CA >> 5) & 03;
#endif
#ifdef L68
            uint level = 0;
#endif
#ifdef WAM
            uint toffset = level * 16;
#endif
            for (uint j = 0; j < 16; j ++)
              {
                cpu_p->Yblock32[j * 2] = 0;
#ifdef WAM
                putbits36_24 (& cpu_p->Yblock32[j * 2],  0,
                           cpu_p->SDWAM[toffset + j].ADDR);
                putbits36_3 (& cpu_p->Yblock32[j * 2], 24,
                           cpu_p->SDWAM[toffset + j].R1);
                putbits36_3 (& cpu_p->Yblock32[j * 2], 27,
                           cpu_p->SDWAM[toffset + j].R2);
                putbits36_3 (& cpu_p->Yblock32[j * 2], 30,
                           cpu_p->SDWAM[toffset + j].R3);
#endif
                cpu_p->Yblock32[j * 2 + 1] = 0;
#ifdef WAM
                putbits36_14 (& cpu_p->Yblock32[j * 2 + 1], 37 - 36,
                           cpu_p->SDWAM[toffset + j].BOUND);
                putbits36_1 (& cpu_p->Yblock32[j * 2 + 1], 51 - 36,
                           cpu_p->SDWAM[toffset + j].R);
                putbits36_1 (& cpu_p->Yblock32[j * 2 + 1], 52 - 36,
                           cpu_p->SDWAM[toffset + j].E);
                putbits36_1 (& cpu_p->Yblock32[j * 2 + 1], 53 - 36,
                           cpu_p->SDWAM[toffset + j].W);
                putbits36_1 (& cpu_p->Yblock32[j * 2 + 1], 54 - 36,
                           cpu_p->SDWAM[toffset + j].P);
                putbits36_1 (& cpu_p->Yblock32[j * 2 + 1], 55 - 36,
                           cpu_p->SDWAM[toffset + j].U);
                putbits36_1 (& cpu_p->Yblock32[j * 2 + 1], 56 - 36,
                           cpu_p->SDWAM[toffset + j].G);
                putbits36_1 (& cpu_p->Yblock32[j * 2 + 1], 57 - 36,
                           cpu_p->SDWAM[toffset + j].C);
                putbits36_14 (& cpu_p->Yblock32[j * 2 + 1], 58 - 36,
                           cpu_p->SDWAM[toffset + j].EB);
#endif
              }
#ifndef WAM
            if (level == 0)
              {
                putbits36 (& cpu_p->Yblock32[0],  0, 24,
                           cpu_p->SDW0.ADDR);
                putbits36 (& cpu_p->Yblock32[0], 24,  3,
                           cpu_p->SDW0.R1);
                putbits36 (& cpu_p->Yblock32[0], 27,  3,
                           cpu_p->SDW0.R2);
                putbits36 (& cpu_p->Yblock32[0], 30,  3,
                           cpu_p->SDW0.R3);
                putbits36 (& cpu_p->Yblock32[0], 37 - 36, 14,
                           cpu_p->SDW0.BOUND);
                putbits36 (& cpu_p->Yblock32[1], 51 - 36,  1,
                           cpu_p->SDW0.R);
                putbits36 (& cpu_p->Yblock32[1], 52 - 36,  1,
                           cpu_p->SDW0.E);
                putbits36 (& cpu_p->Yblock32[1], 53 - 36,  1,
                           cpu_p->SDW0.W);
                putbits36 (& cpu_p->Yblock32[1], 54 - 36,  1,
                           cpu_p->SDW0.P);
                putbits36 (& cpu_p->Yblock32[1], 55 - 36,  1,
                           cpu_p->SDW0.U);
                putbits36 (& cpu_p->Yblock32[1], 56 - 36,  1,
                           cpu_p->SDW0.G);
                putbits36 (& cpu_p->Yblock32[1], 57 - 36,  1,
                           cpu_p->SDW0.C);
                putbits36 (& cpu_p->Yblock32[1], 58 - 36, 14,
                           cpu_p->SDW0.EB);

              }
#endif
          }
          break;

        /// Privileged - Clear Associative Memory

        case x1 (0532):  // camp
          {
            // C(TPR.CA) 16,17 control disabling or enabling the associative
            // memory.
            // This may be done to either or both halves.
            // The full/empty bit of cache PTWAM register is set to zero and
            // the LRU counters are initialized.
#ifdef WAM
            if (! cpu_p->switches.disable_wam)
              { // disabled by simh, do nothing
#ifdef DPS8M
                if (cpu_p->cu.PT_ON) // only clear when enabled
#endif
                    for (uint i = 0; i < N_WAM_ENTRIES; i ++)
                      {
                        cpu_p->PTWAM[i].FE = 0;
#ifdef L68
                        cpu_p->PTWAM[i].USE = (word4) i;
#endif
#ifdef DPS8M
                        cpu_p->PTWAM[i].USE = 0;
#endif
                      }

// 58009997-040 A level of the associative memory is disabled if
// C(TPR.CA) 16,17 = 01
// 58009997-040 A level of the associative memory is enabled if
// C(TPR.CA) 16,17 = 10
// Level j is selected to be enabled/disable if
// C(TPR.CA) 10+j = 1; j=1,2,3,4
// All levels are selected to be enabled/disabled if
// C(TPR.CA) 11,14 = 0
// This is contrary to what AL39 says, so I'm not going to implement it. In
// fact, I'm not even going to implement the halves.

#ifdef DPS8M
                if (cpu_p->TPR.CA != 0000002 && (cpu_p->TPR.CA & 3) != 0)
                  sim_warn ("CAMP ignores enable/disable %06o\n", cpu_p->TPR.CA);
#endif
                if ((cpu_p->TPR.CA & 3) == 02)
                  cpu_p->cu.PT_ON = 1;
                else if ((cpu_p->TPR.CA & 3) == 01)
                  cpu_p->cu.PT_ON = 0;
              }
            else
              {
                cpu_p->PTW0.FE = 0;
                cpu_p->PTW0.USE = 0;
              }
#else
            cpu_p->PTW0.FE = 0;
            cpu_p->PTW0.USE = 0;
#endif
          }
          break;

        case x0 (0532):  // cams
          {
            // The full/empty bit of each SDWAM register is set to zero and the
            // LRU counters are initialized. The remainder of the contents of
            // the registers are unchanged. If the associative memory is
            // disabled, F and LRU are unchanged.
            // C(TPR.CA) 16,17 control disabling or enabling the associative
            // memory.
            // This may be done to either or both halves.
#ifdef WAM
            if (!cpu_p->switches.disable_wam)
              { // disabled by simh, do nothing
#ifdef DPS8M
                if (cpu_p->cu.SD_ON) // only clear when enabled
#endif
                    for (uint i = 0; i < N_WAM_ENTRIES; i ++)
                      {
                        cpu_p->SDWAM[i].FE = 0;
#ifdef L68
                        cpu_p->SDWAM[i].USE = (word4) i;
#endif
#ifdef DPS8M
                        cpu_p->SDWAM[i].USE = 0;
#endif
                      }
// 58009997-040 A level of the associative memory is disabled if
// C(TPR.CA) 16,17 = 01
// 58009997-040 A level of the associative memory is enabled if
// C(TPR.CA) 16,17 = 10
// Level j is selected to be enabled/disable if
// C(TPR.CA) 10+j = 1; j=1,2,3,4
// All levels are selected to be enabled/disabled if
// C(TPR.CA) 11,14 = 0
// This is contrary to what AL39 says, so I'm not going to implement it. In
// fact, I'm not even going to implement the halves.

#ifdef DPS8M
                if (cpu_p->TPR.CA != 0000006 && (cpu_p->TPR.CA & 3) != 0)
                  sim_warn ("CAMS ignores enable/disable %06o\n", cpu_p->TPR.CA);
#endif
                if ((cpu_p->TPR.CA & 3) == 02)
                  cpu_p->cu.SD_ON = 1;
                else if ((cpu_p->TPR.CA & 3) == 01)
                  cpu_p->cu.SD_ON = 0;
              }
            else
              {
                cpu_p->SDW0.FE = 0;
                cpu_p->SDW0.USE = 0;
              }
#else
            cpu_p->SDW0.FE = 0;
            cpu_p->SDW0.USE = 0;
#endif
  }
          break;

        /// Privileged - Configuration and Status

        case x0 (0233):  // rmcm
          {
            // C(TPR.CA)0,2 (C(TPR.CA)1,2 for the DPS 8M processor)
            // specify which processor port (i.e., which system
            // controller) is used.
#ifdef DPS8M
            uint cpu_port_num = (cpu_p->TPR.CA >> 15) & 03;
#endif
#ifdef L68
            uint cpu_port_num = (cpu_p->TPR.CA >> 15) & 07;
#endif
            if (! get_scu_in_use (current_running_cpu_idx, cpu_port_num))
              {
                sim_warn ("rmcm to non-existent controller on "
                          "cpu %d port %d\n",
                          current_running_cpu_idx, cpu_port_num);
                break;
              }
            uint scuUnitIdx = get_scu_idx (current_running_cpu_idx, cpu_port_num);
            t_stat rc = scu_rmcm ((uint) scuUnitIdx,
                                  current_running_cpu_idx,
                                  & cpu_p->rA, & cpu_p->rQ);
            HDBGRegA ();
            HDBGRegQ ();
            if (rc)
              return rc;
            SC_I_ZERO (cpu_p->rA == 0);
            SC_I_NEG (cpu_p->rA & SIGN36);
          }
          break;

        case x0 (0413):  // rscr
          {
            // For the rscr instruction, the first 2 (DPS8M) or 3 (L68) bits of
            // the addr field of the instruction are used to specify which SCU.
            // (2 bits for the DPS8M. (Expect for x6x and x7x below, where 
            // the selected SCU is the one holding the addressed memory).
            
            // According to DH02:
            //   XXXXXX0X  SCU Mode Register (Level 66 only)
            //   XXXXXX1X  Configuration switches
            //   XXXXXn2X  Interrupt mask port n
            //   XXXXXX3X  Interrupt cells
            //   XXXXXX4X  Elapsed time clock
            //   XXXXXX5X  Elapsed time clock
            //   XXXXXX6X  Mode register
            //   XXXXXX7X  Mode register

            // According to privileged_mode_ut,
            //   port*1024 + scr_input*8

            // privileged_mode_ut makes no reference to the special case
            // of x6x and x7x.


            // According to DH02, RSCR in Slave Mode does the CAF
            // without BAR correction, and then forces the CA to 040,
            // resulting in a Clock Read from the SCU on port 0.

            // According to AL93, RSCR in BAR mode is IPR.


//
// Implementing privileged_mode_ut.alm algorithm
//

           // Extract port number
#ifdef DPS8M
            uint cpu_port_num = (cpu_p->TPR.CA >> 10) & 03;
#endif
#ifdef L68
            uint cpu_port_num = (cpu_p->TPR.CA >> 10) & 07;
#endif


            // Trace the cable from the port to find the SCU number
            // connected to that port
            if (! get_scu_in_use (current_running_cpu_idx, cpu_port_num))
              {
                // CPTUR (cptUseFR) -- will be set by doFault

                // Set IAn in Fault register
                if (cpu_port_num == 0)
                  putbits36 (& cpu_p->faultRegister[0], 16, 4, 010);
                else if (cpu_port_num == 1)
                  putbits36 (& cpu_p->faultRegister[0], 20, 4, 010);
                else if (cpu_port_num == 2)
                  putbits36 (& cpu_p->faultRegister[0], 24, 4, 010);
                else
                  putbits36 (& cpu_p->faultRegister[0], 28, 4, 010);

                doFault (cpu_p, FAULT_CMD, fst_cmd_ctl, "(rscr)");
              }
            uint scuUnitIdx = get_scu_idx (current_running_cpu_idx, cpu_port_num);
#ifdef PANEL
            {
               uint function = (cpu_p->iefpFinalAddress >> 3) & 07;
               CPT (cpt13L, function);
            }
#endif
            t_stat rc = scu_rscr ((uint) scuUnitIdx, current_running_cpu_idx,
                                  cpu_p->iefpFinalAddress & MASK15,
                                  & cpu_p->rA, & cpu_p->rQ);
            HDBGRegA ();
            HDBGRegQ ();
            if (rc)
              return rc;
          }
          break;

        case x0 (0231):  // rsw
          {
#ifdef DPS8M
            //if (i->tag == TD_DL)
            word6 rTAG = GET_TAG (IWB_IRODD);
            word6 Td = GET_TD (rTAG);
            word6 Tm = GET_TM (rTAG);
            if (Tm == TM_R && Td == TD_DL)
              {

// 58009997-040 MULTICS Differences Manual DPS 8-70M Aug83
// disagress with Multics source, but probably a typo,
//  0-13 CPU Model Number
// 13-25 CPU Serial Number
// 26-33 Date-Ship code (YYMMDD)
// 34-40 CPU ID Field (reference RSW 2)
//  Byte 40: Bits 03 (Bits 32-35 of RSW 2 Field
//           Bit 4=1 Hex Option included
//           Bit 5=1 RSCR (Clock) is Slave Mode included
//           Bits 6-7 Reserved for later use.
//       50: Operating System Use
// 51-1777(8) To be defined.
// NOTE: There is the possibility of disagreement between the
//       ID bits of RSW 2 and the ID bits of PROM locations
//       35-40. This condition could result when alterable
//       configuration condition is contained in the PROM.
//       The user is adviced to ignore the PROM fields which
//       contain the processor fault vector base (GCOS III)
//       and the processor number and rely on the RSW 2 bits
//       for this purpose. Bits 14-16 of the RSW 2 should be
//       ignored and the bits represnting this information in
//       the PROM should be treated as valid.

// CAC notes: I interpret the fields as
//  0-12 CPU Model Number  // 13 chars, typo
// 13-25 CPU Serial Number // 13 chars
// 26-33 Date-Ship code (YYMMDD) // 8 chars (enough for YYYYMMDD).
// 34-40 CPU ID Field (reference RSW 2)
//  Byte 40: Bits 03 (Bits 32-35 of RSW 2 Field
//           Bit 4=1 Hex Option included
//           Bit 5=1 RSCR (Clock) is Slave Mode included
//           Bits 6-7 Reserved for later use.
//       50: Operating System Use

                unsigned char PROM[1024];
                memset (PROM, 0, sizeof (PROM));
                sprintf ((char *) PROM, "%13s%13d%8s",
                  "DPS8/70M Emul",  //  0-12 CPU Model number
                  cpu_p->switches.serno, // 13-25 CPU Serial number
                  "20160304");      // 26-33 Ship date (YYMMDD)
                word36 tmp = 0;
                tmp |= (word36) ((cpu_p->switches.interlace[0] == 2 ? 1LL : 0LL)
                       << (35- 0));
                tmp |= (word36) ((cpu_p->switches.interlace[1] == 2 ? 1LL : 0LL)
                       << (35- 1));
                tmp |= (word36) ((cpu_p->switches.interlace[2] == 2 ? 1LL : 0LL)
                       << (35- 2));
                tmp |= (word36) ((cpu_p->switches.interlace[3] == 2 ? 1LL : 0LL)
                       << (35- 3));
                tmp |= (word36) ((0b01L)  /* DPS8M */                         
                       << (35- 5));
                tmp |= (word36) ((cpu_p->switches.FLT_BASE & 0177LL)             
                       << (35-12));
                tmp |= (word36) ((0b1L) /* ID_PROM installed */               
                       << (35-13));
                tmp |= (word36) ((0b0000L)                                    
                       << (35-17));
                //tmp |= (word36) ((0b111L)                                   
                       //<< (35-20));
                // According to rsw.incl.pl1, Multics ignores this bit.
                tmp |= (word36) ((0b0L)                                       
                       << (35-18));  //BCD option off
                tmp |= (word36) ((0b1L)                                       
                       << (35-19));  //DPS option
                tmp |= (word36) ((cpu_p->switches.disable_cache ? 0 : 1)                                       
                       << (35-20));  //8K cache not installed
                tmp |= (word36) ((0b00L)                                      
                       << (35-22));
                tmp |= (word36) ((0b1L)  /* DPS8M */                          
                       << (35-23));
                tmp |= (word36) ((cpu_p->switches.proc_mode & 01LL)              
                       << (35-24));
                tmp |= (word36) ((0b0L)                                       
                       << (35-25)); // new product line (CPL/NPL)
                tmp |= (word36) ((0b000L)                                     
                       << (35-28));
                tmp |= (word36) ((cpu_p->switches.proc_speed & 017LL)            
                       << (35-32));
                tmp |= (word36) ((cpu_p->switches.cpu_num & 07LL)                
                       << (35-35));
                // 36: bits 00-07
                PROM[36] = getbits36_8 (tmp, 0);
                // 37: bits 08-15
                PROM[37] = getbits36_8 (tmp, 8);
                // 38: bits 16-23
                PROM[38] = getbits36_8 (tmp, 16);
                // 39: bits 24-31
                PROM[39] = getbits36_8 (tmp, 24);
                // 40: bits 32-35
                // 40: bits 0-3: bits 32-35 of RSW 2 field 
                //     (this is dps8m, so only 32 is always 0)
                //            4: hex option
                //            5: RSCR clock is slave
                //          6-7: reserved
                PROM[40] = ((unsigned char) ((tmp & 017) << 4))
                   // | 0100  // hex option
                   // | 0040  // clock is slave
                  ;
                            
                cpu_p->rA = PROM[cpu_p->TPR.CA & 1023];
                break;
              }
#endif // DPS8M
            uint select = cpu_p->TPR.CA & 0x7;
            switch (select)
              {
                case 0: // data switches
                  cpu_p->rA = cpu_p->switches.data_switches;
                  break;

                case 1: // configuration switches for ports A, B, C, D
// y = 1:
//
//   0               0 0               1 1               2 2               3
//   0               8 9               7 8               6 7               5
//  -------------------------------------------------------------------------
//  |      PORT A     |     PORT B      |     PORT C      |     PORT D      |
//  -------------------------------------------------------------------------
//  | ADR |j|k|l| MEM | ADR |j|k|l| MEM | ADR |j|k|l| MEM | ADR |j|k|l| MEM |
//  -------------------------------------------------------------------------
//
//
//   ADR: Address assignment switch setting for port
//         This defines the base address for the SCU
//   j: port enabled flag
//   k: system initialize enabled flag
//   l: interface enabled flag
//   MEM coded memory size
//     000 32K     2^15
//     001 64K     2^16
//     010 128K    2^17
//     011 256K    2^18
//     100 512K    2^19
//     101 1024K   2^20
//     110 2048K   2^21
//     111 4096K   2^22

                  cpu_p->rA  = 0;
                  cpu_p->rA |= (word36) (cpu_p->switches.assignment  [0] & 07LL)
                            << (35 -  (2 +  0));
                  cpu_p->rA |= (word36) (cpu_p->switches.enable      [0] & 01LL)
                            << (35 -  (3 +  0));
                  cpu_p->rA |= (word36) (cpu_p->switches.init_enable [0] & 01LL)
                            << (35 -  (4 +  0));
                  cpu_p->rA |= (word36) (cpu_p->switches.interlace   [0] ? 1LL:0LL)
                            << (35 -  (5 +  0));
                  cpu_p->rA |= (word36) (cpu_p->switches.store_size  [0] & 07LL)
                            << (35 -  (8 +  0));

                  cpu_p->rA |= (word36) (cpu_p->switches.assignment  [1] & 07LL)
                            << (35 -  (2 +  9));
                  cpu_p->rA |= (word36) (cpu_p->switches.enable      [1] & 01LL)
                            << (35 -  (3 +  9));
                  cpu_p->rA |= (word36) (cpu_p->switches.init_enable [1] & 01LL)
                            << (35 -  (4 +  9));
                  cpu_p->rA |= (word36) (cpu_p->switches.interlace   [1] ? 1LL:0LL)
                            << (35 -  (5 +  9));
                  cpu_p->rA |= (word36) (cpu_p->switches.store_size  [1] & 07LL)
                            << (35 -  (8 +  9));

                  cpu_p->rA |= (word36) (cpu_p->switches.assignment  [2] & 07LL)
                            << (35 -  (2 + 18));
                  cpu_p->rA |= (word36) (cpu_p->switches.enable      [2] & 01LL)
                            << (35 -  (3 + 18));
                  cpu_p->rA |= (word36) (cpu_p->switches.init_enable [2] & 01LL)
                            << (35 -  (4 + 18));
                  cpu_p->rA |= (word36) (cpu_p->switches.interlace   [2] ? 1LL:0LL)
                            << (35 -  (5 + 18));
                  cpu_p->rA |= (word36) (cpu_p->switches.store_size  [2] & 07LL)
                            << (35 -  (8 + 18));

                  cpu_p->rA |= (word36) (cpu_p->switches.assignment  [3] & 07LL)
                            << (35 -  (2 + 27));
                  cpu_p->rA |= (word36) (cpu_p->switches.enable      [3] & 01LL)
                            << (35 -  (3 + 27));
                  cpu_p->rA |= (word36) (cpu_p->switches.init_enable [3] & 01LL)
                            << (35 -  (4 + 27));
                  cpu_p->rA |= (word36) (cpu_p->switches.interlace   [3] ? 1LL:0LL)
                            << (35 -  (5 + 27));
                  cpu_p->rA |= (word36) (cpu_p->switches.store_size  [3] & 07LL)
                            << (35 -  (8 + 27));
                  break;

                case 2: // fault base and processor number  switches
// y = 2:
//
//   0     0 0 0 0            1 1 1     1 1 1 2 2 2 2 2 2 2   2 2     3 3   3
//   0     3 4 5 6            2 3 4     7 8 9 0 1 2 3 4 5 6   8 9     2 3   5
//  --------------------------------------------------------------------------
//  |A|B|C|D|   |              | |       | | | |   | | | |     |       |     |
//  --------- b |   FLT BASE   |c|0 0 0 0|d|e|f|0 0|g|h|i|0 0 0| SPEED | CPU |
//  |a|a|a|a|   |              | |       | | | |   | | | |     |       |     |
//  --------------------------------------------------------------------------
//

//   a: port A-D is 0: 4 word or 1: 2 word
//   b: processor type 0:L68 or DPS, 1: DPS8M, 2,3: reserved for future use
//   c: id prom 0: not installed, 1: installed
//   d: 1: bcd option installed (marketing designation)
//   e: 1: dps option installed (marketing designation)
//   f: 1: 8k cache installed
//   g: processor type designation: 0: dps8/xx, 1: dps8m/xx
//   h: gcos/vms switch position: 0:GCOS mode 1: virtual mode
//   i: current or new product line peripheral type: 0:CPL, 1:NPL
//   SPEED: 0000 = 8/70, 0100 = 8/52
//   CPU: Processor number
// DPS 8M processors:
// C(Port interlace, Ports A-D) -> C(A) 0,3
// 01 -> C(A) 4,5
// C(Fault base switches) -> C(A) 6,12
// 1 -> C(A) 13
// 0000 -> C(A) 14,17
// 111 -> C(A) 18,20
// 00 -> C(A) 21,22
// 1 -> C(A) 23
// C(Processor mode sw) -> C(A) 24
// 1 -> C(A) 25
// 000 -> C(A) 26,28
// C(Processor speed) -> C (A) 29,32



// C(Processor number switches) -> C(A) 33,35

// According to bound_gcos_.1.s.archive/gcos_fault_processor_.pl1 (L68/DPS):
//
// /* Set the A register to reflect switch info. */
//                          mc.regs.a =
// 
// /* (A-reg bits) */
// /* (0-3) Port address expansion option:           */ (4)"0"b
// /* (4-5) Reserved for future use:                 */ || (2)"0"b
// /* (6-12) Processor fault base address switches:  */ || (7)"0"b
// /* (13-16) L66 peripheral connectability:         */ || (4)"0"b
// /* (17) Future use (must be zero):                */ || (1)"1"b
// /* (18) BCD option installed:                     */ || (1)"1"b
// /* (19) DPS type processor:                       */ || (1)"0"b
// /* (20) 8K cache option installed:                */ || (1)"0"b
// /* (21) Gear shift model processor:               */ || (1)"0"b
// /* (22) Power pach option installed:              */ || (1)"0"b
// /* (23) VMS-CU option installed - 66B' proc:      */ || (1)"0"b
// /* (24) VMS-VU option installed - 66B proc:       */ || (1)"0"b
// /* (25) Type processor (0) CPL, (1) DPSE-NPL:     */ || (1)"0"b
// /* (26) 6025, 6605 or 6610 type processor:        */ || (1)"0"b
// /* (27) 2K cache option installed:                */ || (1)"0"b
// /* (28) Extended memory option installed:         */ || (1)"0"b
// /* (29-30) cabinet (00) 8/70, (01) 8/52, (10) 862, (11) 846:          */ || (2)"0"b
// /* (31) EIS option installed:                     */ || (1)"1"b
// /* (32) (1) slow memory access, (0) fast memory:  */ || (1)"0"b
// /* (33) (1) no instruction overlap, (0) overlap:  */ || (1)"0"b
// /* (34-35) Processor number:                      */ ||unspec (mc.cpu_type);

                  cpu_p->rA = 0;
#ifdef DPS8M
                  cpu_p->rA |= (word36) ((cpu_p->switches.interlace[0] == 2 ?
                            1LL : 0LL) << (35- 0));
                  cpu_p->rA |= (word36) ((cpu_p->switches.interlace[1] == 2 ?
                            1LL : 0LL) << (35- 1));
                  cpu_p->rA |= (word36) ((cpu_p->switches.interlace[2] == 2 ?
                            1LL : 0LL) << (35- 2));
                  cpu_p->rA |= (word36) ((cpu_p->switches.interlace[3] == 2 ?
                            1LL : 0LL) << (35- 3));
#endif

#ifdef DPS8M
                  cpu_p->rA |= (word36) ((0b01L)  /* DPS8M */
                             << (35- 5));
#endif
#ifdef L68
                  cpu_p->rA |= (word36) ((0b00L)  /* L68/DPS */
                             << (35- 5));
#endif
                  cpu_p->rA |= (word36) ((cpu_p->switches.FLT_BASE & 0177LL)
                             << (35-12));
#ifdef DPS8M
                  cpu_p->rA |= (word36) ((0b1L) /* ID_PROM installed */
                             << (35-13));
#endif
                  cpu_p->rA |= (word36) ((0b0000L) 
                            << (35-17));
                  //cpu_p->rA |= (word36) ((0b111L)
                              //<< (35-20));
                  // According to rsw.incl.pl1, Multics ignores this bit.
                  cpu_p->rA |= (word36) ((0b0L)
                            << (35-18));  //BCD option off
#ifdef DPS8M
                  cpu_p->rA |= (word36) ((0b1L)
                            << (35-19));  // L68/DPS option: DPS
#endif
#ifdef L68
                  cpu_p->rA |= (word36) ((0b0L)
                            << (35-19));  // L68/DPS option: L68
#endif
#ifdef DPS8M
                  cpu_p->rA |= (word36) ((cpu_p->switches.disable_cache ? 0 : 1)
                            << (35-20));  //8K cache not installed
                  cpu_p->rA |= (word36) ((0b00L)
                            << (35-22));
                  cpu_p->rA |= (word36) ((0b1L)  /* DPS8M */
                            << (35-23));
                  cpu_p->rA |= (word36) ((cpu_p->switches.proc_mode & 01LL)
                            << (35-24));
                  cpu_p->rA |= (word36) ((0b0L)
                            << (35-25)); // new product line (CPL/NPL)
                  cpu_p->rA |= (word36) ((0b000L)
                            << (35-28));
                  cpu_p->rA |= (word36) ((cpu_p->switches.proc_speed & 017LL)
                            << (35-32));
#endif
#ifdef L68
                  cpu_p->rA |= (word36) ((0b0L)
                            << (35-27)); // 2K cache disabled
                  cpu_p->rA |= (word36) ((0b0L)
                            << (35-28)); // GCOS mode extended memory disabled
                  cpu_p->rA |= (word36) ((0b1110L)
                            << (35-32)); // CPU ID
#endif
                  cpu_p->rA |= (word36) ((cpu_p->switches.cpu_num & 07LL)
                            << (35-35));
                  break;

                case 3: // configuration switches for ports E, F, G, H
#ifdef DPS8M
                  cpu_p->rA = 0;
                  break;
#endif
#ifdef L68
// y = 3:
//
//   0               0 0               1 1               2 2               3
//   0               8 9               7 8               6 7               5
//  -------------------------------------------------------------------------
//  |      PORT E     |     PORT F      |     PORT G      |     PORT H      |
//  -------------------------------------------------------------------------
//  | ADR |j|k|l| MEM | ADR |j|k|l| MEM | ADR |j|k|l| MEM | ADR |j|k|l| MEM |
//  -------------------------------------------------------------------------
//
//
//   ADR: Address assignment switch setting for port
//         This defines the base address for the SCU
//   j: port enabled flag
//   k: system initialize enabled flag
//   l: interface enabled flag
//   MEM coded memory size
//     000 32K     2^15
//     001 64K     2^16
//     010 128K    2^17
//     011 256K    2^18
//     100 512K    2^19
//     101 1024K   2^20
//     110 2048K   2^21
//     111 4096K   2^22

                  cpu_p->rA  = 0;
                  cpu_p->rA |= (word36) (cpu_p->switches.assignment  [4] & 07LL)
                            << (35 -  (2 +  0));
                  cpu_p->rA |= (word36) (cpu_p->switches.enable      [4] & 01LL)
                            << (35 -  (3 +  0));
                  cpu_p->rA |= (word36) (cpu_p->switches.init_enable [4] & 01LL)
                            << (35 -  (4 +  0));
                  cpu_p->rA |= (word36) (cpu_p->switches.interlace   [4] ? 1LL:0LL)
                            << (35 -  (5 +  0));
                  cpu_p->rA |= (word36) (cpu_p->switches.store_size  [4] & 07LL)
                            << (35 -  (8 +  0));

                  cpu_p->rA |= (word36) (cpu_p->switches.assignment  [5] & 07LL)
                            << (35 -  (2 +  9));
                  cpu_p->rA |= (word36) (cpu_p->switches.enable      [5] & 01LL)
                            << (35 -  (3 +  9));
                  cpu_p->rA |= (word36) (cpu_p->switches.init_enable [5] & 01LL)
                            << (35 -  (4 +  9));
                  cpu_p->rA |= (word36) (cpu_p->switches.interlace   [5] ? 1LL:0LL)
                            << (35 -  (5 +  9));
                  cpu_p->rA |= (word36) (cpu_p->switches.store_size  [5] & 07LL)
                            << (35 -  (8 +  9));

                  cpu_p->rA |= (word36) (cpu_p->switches.assignment  [6] & 07LL)
                            << (35 -  (2 + 18));
                  cpu_p->rA |= (word36) (cpu_p->switches.enable      [6] & 01LL)
                            << (35 -  (3 + 18));
                  cpu_p->rA |= (word36) (cpu_p->switches.init_enable [6] & 01LL)
                            << (35 -  (4 + 18));
                  cpu_p->rA |= (word36) (cpu_p->switches.interlace   [6] ? 1LL:0LL)
                            << (35 -  (5 + 18));
                  cpu_p->rA |= (word36) (cpu_p->switches.store_size  [6] & 07LL)
                            << (35 -  (8 + 18));

                  cpu_p->rA |= (word36) (cpu_p->switches.assignment  [7] & 07LL)
                            << (35 -  (2 + 27));
                  cpu_p->rA |= (word36) (cpu_p->switches.enable      [7] & 01LL)
                            << (35 -  (3 + 27));
                  cpu_p->rA |= (word36) (cpu_p->switches.init_enable [7] & 01LL)
                            << (35 -  (4 + 27));
                  cpu_p->rA |= (word36) (cpu_p->switches.interlace   [7] ? 1LL:0LL)
                            << (35 -  (5 + 27));
                  cpu_p->rA |= (word36) (cpu_p->switches.store_size  [7] & 07LL)
                            << (35 -  (8 + 27));
                  break;

#endif

                case 4:
                  // I suspect the this is a L68 only, but AL39 says both
                  // port interlace and half/full size
                  // The DPS doesn't seem to have the half/full size switches
                  // so we'll always report full, and the interlace bits were
                  // squeezed into RSW 2

//  0                       1 1 1 1 1 1 1 1 2 2 2 2 2 2 2 2 2 2           3
//  0                       2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9           5
// -------------------------------------------------------------------------
// |                         | A | B | C | D | E | F | G | H |             |
// |0 0 0 0 0 0 0 0 0 0 0 0 0---------------------------------0 0 0 0 0 0 0|
// |                         |f|g|f|g|f|g|f|g|f|g|f|g|f|g|f|g|             |
// -------------------------------------------------------------------------
//                         13 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1             7

                  cpu_p->rA  = 0;
                  cpu_p->rA |= (word36) (cpu_p->switches.interlace [0] == 2 ?
                            1LL : 0LL) << (35-13);
                  cpu_p->rA |= (word36) (cpu_p->switches.interlace [1] == 2 ?
                            1LL : 0LL) << (35-15);
                  cpu_p->rA |= (word36) (cpu_p->switches.interlace [2] == 2 ?
                            1LL : 0LL) << (35-17);
                  cpu_p->rA |= (word36) (cpu_p->switches.interlace [3] == 2 ?
                            1LL : 0LL) << (35-19);
#ifdef L68
                  cpu_p->rA |= (word36) (cpu_p->switches.interlace [4] == 2 ?
                            1LL : 0LL) << (35-21);
                  cpu_p->rA |= (word36) (cpu_p->switches.interlace [5] == 2 ?
                            1LL : 0LL) << (35-23);
                  cpu_p->rA |= (word36) (cpu_p->switches.interlace [6] == 2 ?
                            1LL : 0LL) << (35-25);
                  cpu_p->rA |= (word36) (cpu_p->switches.interlace [7] == 2 ?
                            1LL : 0LL) << (35-27);
#endif
                  break;

                default:
                  // XXX Guessing values; also don't know if this is actually
                  //  a fault
                  doFault (cpu_p, FAULT_IPR,
                           fst_ill_mod,
                           "Illegal register select value");
              }
            HDBGRegA ();
            SC_I_ZERO (cpu_p->rA == 0);
            SC_I_NEG (cpu_p->rA & SIGN36);
          }
          break;

        /// Privileged - System Control

        case x0 (0015):  // cioc
          {
            // cioc The system controller addressed by Y (i.e., contains
            // the word at Y) sends a connect signal to the port specified
            // by C(Y) 33,35.
#ifdef SCUMEM
            word24 offset;
            int cpu_port_num = lookup_cpu_mem_map (cpu_p->iefpFinalAddress, & offset);
#else
            int cpu_port_num = lookup_cpu_mem_map (cpu_p, cpu_p->iefpFinalAddress);
#endif
            // If the there is no port to that memory location, fault
            if (cpu_port_num < 0)
              {
                doFault (cpu_p, FAULT_ONC, fst_onc_nem, "(cioc)");
              }
            if (! get_scu_in_use (current_running_cpu_idx, cpu_port_num))
              {
                doFault (cpu_p, FAULT_ONC, fst_onc_nem, "(cioc)");
              }
            uint scuUnitIdx = get_scu_idx (current_running_cpu_idx, cpu_port_num);

// expander word
// dcl  1 scs$reconfig_general_cow aligned external, /* Used during reconfig
//                                                      ops. */
//   2 pad bit (36) aligned,
//   2 cow,                        /* Connect operand word, in odd location. */
//   3 sub_mask bit (8) unaligned, /* Expander sub-port mask */
//   3 mbz1 bit (13) unaligned,
//   3 expander_command bit (3) unaligned,   /* Expander command. */
//   3 mbz2 bit (9) unaligned,
//   3 controller_port fixed bin (3) unaligned unsigned;/* controller port for
//                                                          this CPU */

            word8 sub_mask = getbits36_8 (cpu_p->CY, 0);
            word3 expander_command = getbits36_3 (cpu_p->CY, 21);
            uint scu_port_num = (uint) getbits36_3 (cpu_p->CY, 33);
            scu_cioc (current_running_cpu_idx, (uint) scuUnitIdx, scu_port_num, 
                      expander_command, sub_mask);
          }
          break;

        case x0 (0553):  // smcm
          {
            // C(TPR.CA)0,2 (C(TPR.CA)1,2 for the DPS 8M processor)
            // specify which processor port (i.e., which system
            // controller) is used.
#ifdef DPS8M
            uint cpu_port_num = (cpu_p->TPR.CA >> 15) & 03;
#endif
#ifdef L68
            uint cpu_port_num = (cpu_p->TPR.CA >> 15) & 07;
#endif
            if (! get_scu_in_use (current_running_cpu_idx, cpu_port_num))
              {
                sim_warn ("smcm to non-existent controller on "
                          "cpu %d port %d\n", 
                          current_running_cpu_idx, cpu_port_num);
                break;
              }
            uint scuUnitIdx = get_scu_idx (current_running_cpu_idx, cpu_port_num);
            t_stat rc = scu_smcm ((uint) scuUnitIdx,
                                  current_running_cpu_idx, cpu_p->rA, cpu_p->rQ);
            if (rc)
              return rc;
          }
          break;

        case x0 (0451):  // smic
          {
            // For the smic instruction, the first 2 or 3 bits of the addr
            // field of the instruction are used to specify which SCU.
            // 2 bits for the DPS8M.
            //int scuUnitIdx = getbits36_2 (TPR.CA, 0);

            // C(TPR.CA)0,2 (C(TPR.CA)1,2 for the DPS 8M processor)
            // specify which processor port (i.e., which system
            // controller) is used.
#ifdef DPS8M
            uint cpu_port_num = (cpu_p->TPR.CA >> 15) & 03;
#endif
#ifdef L68
            uint cpu_port_num = (cpu_p->TPR.CA >> 15) & 07;
#endif
            if (! get_scu_in_use (current_running_cpu_idx, cpu_port_num))
              {
#ifdef DPS8M
                return SCPE_OK;
#endif 
#ifdef L68
                // CPTUR (cptUseFR) -- will be set by doFault
                if (cpu_port_num == 0)
                  putbits36_4 (& cpu_p->faultRegister[0], 16, 010);
                else if (cpu_port_num == 1)
                  putbits36_4 (& cpu_p->faultRegister[0], 20, 010);
                else if (cpu_port_num == 2)
                  putbits36_4 (& cpu_p->faultRegister[0], 24, 010);
                else if (cpu_port_num == 3)
                  putbits36 (& cpu_p->faultRegister[0], 28, 4, 010);
// XXX What if the port is > 3?
                doFault (cpu_p, FAULT_CMD, fst_cmd_ctl, "(smic)");
#endif
              }
            uint scuUnitIdx = get_scu_idx (current_running_cpu_idx, cpu_port_num);
            t_stat rc = scu_smic ((uint) scuUnitIdx, current_running_cpu_idx, 
                                  cpu_port_num, cpu_p->rA);
            if (rc)
              return rc;
          }
          break;

        case x0 (0057):  // sscr
          {
            //uint cpu_port_num = (cpu_p->TPR.CA >> 15) & 03;
            // Looking at privileged_mode_ut.alm, shift 10 bits...
#ifdef DPS8M
            uint cpu_port_num = (cpu_p->TPR.CA >> 10) & 03;
#endif
#ifdef L68
            uint cpu_port_num = (cpu_p->TPR.CA >> 10) & 07;
#endif
            if (! get_scu_in_use (current_running_cpu_idx, cpu_port_num))
              {
                // CPTUR (cptUseFR) -- will be set by doFault
                if (cpu_port_num == 0)
                  putbits36_4 (& cpu_p->faultRegister[0], 16, 010);
                else if (cpu_port_num == 1)
                  putbits36_4 (& cpu_p->faultRegister[0], 20, 010);
                else if (cpu_port_num == 2)
                  putbits36_4 (& cpu_p->faultRegister[0], 24, 010);
                else
                  putbits36 (& cpu_p->faultRegister[0], 28, 4, 010);
                doFault (cpu_p, FAULT_CMD, fst_cmd_ctl, "(sscr)");
              }
            uint scuUnitIdx = get_scu_idx (current_running_cpu_idx, cpu_port_num);
            t_stat rc = scu_sscr ((uint) scuUnitIdx, current_running_cpu_idx,
                                  cpu_port_num, cpu_p->iefpFinalAddress & MASK15,
                                  cpu_p->rA, cpu_p->rQ);

            if (rc)
              return rc;
          }
          break;

        // Privileged - Miscellaneous

        case x0 (0212):  // absa
          {
            word36 result;
            int rc = doABSA (cpu_p, & result);
            if (rc)
              return rc;
            cpu_p->rA = result;
            HDBGRegA ();
            SC_I_ZERO (cpu_p->rA == 0);
            SC_I_NEG (cpu_p->rA & SIGN36);
          }
          break;

        case x0 (0616):  // dis

          if (! cpu_p->switches.dis_enable)
            {
              return STOP_STOP;
            }

          // XXX This is subtle; g7Pending below won't see the queued
          // g7Fault. I don't understand how the real hardware dealt 
          // with this, but this seems to work. (I would hazard a guess
          // that DIS was doing a continuous FETCH/EXECUTE cycle 
          // ('if !interrupt goto .'))
          advanceG7Faults (cpu_p);

          if ((! cpu_p->switches.tro_enable) &&
              (! sample_interrupts (cpu_p)) &&
              (sim_qcount () == 0))  // XXX If clk_svc is implemented it will
                                     // break this logic
            {
              sim_printf ("DIS@0%06o with no interrupts pending and"
                          " no events in queue\n", cpu_p->PPR.IC);
              sim_printf ("\nCycles = %"PRId64"\n", cpu_p->cycleCnt);
              sim_printf ("\nInstructions = %"PRId64"\n", cpu_p->cycleCnt);
              longjmp (cpu_p->jmpMain, JMP_STOP);
            }

// Multics/BCE halt
          if (cpu_p->PPR.PSR == 0430 && cpu_p->PPR.IC == 012)
              {
                sim_printf ("BCE DIS causes CPU halt\n");
                sim_debug (DBG_MSG, & cpu_dev, "BCE DIS causes CPU halt\n");
                longjmp (cpu_p->jmpMain, JMP_STOP);
              }

#ifdef ROUND_ROBIN
          if (cpu_p->PPR.PSR == 034 && cpu_p->PPR.IC == 03535)
              {
                sim_printf ("[%lld] sys_trouble$die  DIS causes CPU halt\n", cpu_p->cycleCnt);
                sim_debug (DBG_MSG, & cpu_dev, "BCE DIS causes CPU halt\n");
                //longjmp (cpu_p->jmpMain, JMP_STOP);
                cpu_p->isRunning = false;
              }
#endif
          if (i->address == 0777)
              {
                sim_printf ("Multics DIS disables CPU: CA: 0x%x\n",cpu_p->TPR.CA);
                sim_debug (DBG_MSG, & cpu_dev, "Multics DIS disables CPU\n");
                longjmp (cpu_p->jmpMain, JMP_STOP);
              }

          sim_debug (DBG_TRACEEXT, & cpu_dev, "entered DIS_cycle\n");
          //sim_printf ("entered DIS_cycle\n");

          // No operation takes place, and the processor does not
          // continue with the next instruction; it waits for a
          // external interrupt signal.
          // AND, according to pxss.alm, TRO

// Bless NovaScale...
//  DIS
//
//    NOTES:
//
//      1. The inhibit bit in this instruction only affects the recognition
//         of a Timer Runout (TROF) fault.
//
//         Inhibit ON delays the recognition of a TROF until the processor
//         enters Slave mode.
//
//         Inhibit OFF allows the TROF to interrupt the DIS state.
//
//      2. For all other faults and interrupts, the inhibit bit is ignored.
//
//      3. The use of this instruction in the Slave or Master mode causes a
//         Command fault.

          if (sample_interrupts (cpu_p))
            {
              sim_debug (DBG_TRACEEXT, & cpu_dev, "DIS sees an interrupt\n");
              cpu_p->interrupt_flag = true;
              break;
            }
// Implementing TRO according to AL39 for the DIS cause caues idle systems to
// hang in the DIS instruction. Revert back to the old behavior.
#if 1
          if (GET_I (cpu_p->cu.IWB) ? bG7PendingNoTRO (cpu_p) : bG7Pending (cpu_p))
#else
          //if (GET_I (cpu_p->cu.IWB) ? bG7PendingNoTRO () : bG7Pending ())
          // Don't check timer runout if in absolute mode, privledged, or
          // interrupts inhibited.
          bool noCheckTR = is_priv_mode (cpu_p)  ||
                            GET_I (cpu_p->cu.IWB);
          if (noCheckTR ? bG7PendingNoTRO () : bG7Pending ())
#endif
            {
              sim_debug (DBG_TRACEEXT, & cpu_dev, "DIS sees a TRO\n");
              cpu_p->g7_flag = true;
              break;
            }
          else
            {
              sim_debug (DBG_TRACEEXT, & cpu_dev, "DIS refetches\n");
#ifdef ROUND_ROBIN
#ifdef ISOLTS
              if (current_running_cpu_idx)
              {
//sim_printf ("stopping CPU %c\n", current_running_cpu_idx + 'A');
                cpu_p->isRunning = false;
              }
#endif
#endif
              return CONT_DIS;
            }

        /// POINTER REGISTER INSTRUCTIONS

        /// PRIVILEGED INSTRUCTIONS

        /// Privileged - Register Load

        /// Privileged - Clear Associative Memory

        /// EIS - Address Register Load

                         // aarn
        case x1 (0560):  // aar0
        case x1 (0561):  // aar1
        case x1 (0562):  // aar2
        case x1 (0563):  // aar3
        case x1 (0564):  // aar4
        case x1 (0565):  // aar5
        case x1 (0566):  // aar6
        case x1 (0567):  // aar7
          {
            // For n = 0, 1, ..., or 7 as determined by operation code
            PNL (L68_ (DU_CYCLE_DDU_LDEA;))

            if (getbits36_1 (cpu_p->CY, 23) != 0)
              doFault (cpu_p, FAULT_IPR,
                       fst_ill_proc,
                       "aarn C(Y)23 != 0");

            uint32 n = opcode10 & 07;  // get
            CPTUR (cptUsePRn + n);

            // C(Y)0,17 -> C(ARn.WORDNO)
            cpu_p->AR[n].WORDNO = GETHI (cpu_p->CY);

            uint TA = getbits36_2 (cpu_p->CY, 21);
            uint CN = getbits36_3 (cpu_p->CY, 18);

            switch (TA)
              {
                case CTA4:  // 2
                  // If C(Y)21,22 = 10 (TA code = 2), then
                  //   C(Y)18,20 / 2 -> C(ARn.CHAR)
                  //   4 * (C(Y)18,20)mod2 + 1 -> C(ARn.BITNO)

                  // According to AL39, CN is translated:
                  //  CN   CHAR  BIT
                  //   0      0    1
                  //   1      0    5
                  //   2      1    1
                  //   3      1    5
                  //   4      2    1
                  //   5      2    5
                  //   6      3    1
                  //   7      3    5
                  //SET_AR_CHAR_BITNO (n, CN/2, 4 * (CN % 2) + 1);

                  // According to ISOLTS ps805
                  //  CN   CHAR  BIT
                  //   0      0    0
                  //   1      0    5
                  //   2      1    0
                  //   3      1    5
                  //   4      2    0
                  //   5      2    5
                  //   6      3    0
                  //   7      3    5
                  SET_AR_CHAR_BITNO (n, (word2) (CN/2), (CN % 2) ? 5 : 0);
                        
                  break;

                case CTA6:  // 1
                  // If C(Y)21,22 = 01 (TA code = 1) and C(Y)18,20 = 110
                  // or 111 an illegal procedure fault occurs.
                  if (CN > 5)
                    {
                      cpu_p->AR[n].WORDNO = 0;
                      SET_AR_CHAR_BITNO (n, 0, 0);
                      doFault (cpu_p, FAULT_IPR, fst_ill_proc, "aarn TN > 5");
                    }

                  // If C(Y)21,22 = 01 (TA code = 1), then
                  //   (6 * C(Y)18,20) / 9 -> C(ARn.CHAR)
                  //   (6 * C(Y)18,20)mod9 -> C(ARn.BITNO)
                  SET_AR_CHAR_BITNO (n, (word2) ((6 * CN) / 9),
                                     (6 * CN) % 9);
                  break;

                case CTA9:  // 0
                  // If C(Y)21,22 = 00 (TA code = 0), then
                  //   C(Y)18,19 -> C(ARn.CHAR)
                  //   0000 -> C(ARn.BITNO)
                  // remember, 9-bit CN's are funky
                  SET_AR_CHAR_BITNO (n, (word2) (CN >> 1), 0);
                  break;

                case CTAILL: // 3
                  // If C(Y)21,22 = 11 (TA code = 3) an illegal procedure
                  // fault occurs.
                  cpu_p->AR[n].WORDNO = 0;
                  SET_AR_CHAR_BITNO (n, 0, 0);
                  HDBGRegAR (n);
                  doFault (cpu_p, FAULT_IPR, fst_ill_proc, "aarn TA = 3");
              }
            HDBGRegAR (n);
          }
#ifdef TEST_OLIN
          cmpxchg ();
#endif
          break;

        // Load Address Register n
                        // larn
        case x1 (0760): // lar0
        case x1 (0761): // lar1
        case x1 (0762): // lar2
        case x1 (0763): // lar3
        case x1 (0764): // lar4
        case x1 (0765): // lar5
        case x1 (0766): // lar6
        case x1 (0767): // lar7
          {
            // For n = 0, 1, ..., or 7 as determined by operation code
            //    C(Y)0,23 -> C(ARn)
            PNL (L68_ (DU_CYCLE_DDU_LDEA;))

            uint32 n = opcode10 & 07;  // get n
            CPTUR (cptUsePRn + n);
            cpu_p->AR[n].WORDNO = GETHI (cpu_p->CY);
// AL-38 implies CHAR/BITNO, but ISOLTS requires PR.BITNO.
            SET_AR_CHAR_BITNO (n,  getbits36_2 (cpu_p->CY, 18),
                               getbits36_4 (cpu_p->CY, 20));
            HDBGRegAR (n);
          }
          break;

        // lareg - Load Address Registers

        case x1 (0463):  // lareg
          PNL (L68_ (DU_CYCLE_DDU_LDEA;))

          for (uint32 n = 0 ; n < 8 ; n += 1)
            {
              CPTUR (cptUsePRn + n);
              word36 tmp36 = cpu_p->Yblock8[n];
              cpu_p->AR[n].WORDNO = getbits36_18 (tmp36, 0);
              SET_AR_CHAR_BITNO (n,  getbits36_2 (tmp36, 18),
                                 getbits36_4 (tmp36, 20));
              HDBGRegAR (n);
            }
          break;

        // lpl - Load Pointers and Lengths

        case x1 (0467):  // lpl
          PNL (L68_ (DU_CYCLE_DDU_LDEA;))
          words2du (cpu_p, cpu_p->Yblock8);
          break;

        // narn -  (G'Kar?) Numeric Descriptor to Address Register n
                        // narn
        case x1 (0660): // nar0
        case x1 (0661): // nar1
        case x1 (0662): // nar2
        case x1 (0663): // nar3
        case x1 (0664): // nar4
        case x1 (0665): // nar5
        case x1 (0666): // nar6 beware!!!! :-)
        case x1 (0667): // nar7
          {
            // For n = 0, 1, ..., or 7 as determined by operation code
            PNL (L68_ (DU_CYCLE_DDU_LDEA;))

            uint32 n = opcode10 & 07;  // get
            CPTUR (cptUsePRn + n);

            // C(Y)0,17 -> C(ARn.WORDNO)
            cpu_p->AR[n].WORDNO = GETHI (cpu_p->CY);

            uint TN = getbits36_1 (cpu_p->CY, 21); // C(Y) 21
            uint CN = getbits36_3 (cpu_p->CY, 18); // C(Y) 18-20

            switch(TN)
              {
                case CTN4:   // 1
                    // If C(Y)21 = 1 (TN code = 1), then
                    //   (C(Y)18,20) / 2 -> C(ARn.CHAR)
                    //   4 * (C(Y)18,20)mod2 + 1 -> C(ARn.BITNO)

                    // According to AL39, CN is translated:
                    //  CN   CHAR  BIT
                    //   0      0    1
                    //   1      0    5
                    //   2      1    1
                    //   3      1    5
                    //   4      2    1
                    //   5      2    5
                    //   6      3    1
                    //   7      3    5
                    //SET_AR_CHAR_BITNO (n, CN/2, 4 * (CN % 2) + 1);

                    // According to ISOLTS ps805
                    //  CN   CHAR  BIT
                    //   0      0    0
                    //   1      0    5
                    //   2      1    0
                    //   3      1    5
                    //   4      2    0
                    //   5      2    5
                    //   6      3    0
                    //   7      3    5
                    SET_AR_CHAR_BITNO (n, (word2) (CN/2), (CN % 2) ? 5 : 0);
                        
                    break;

                case CTN9:  // 0
                  // If C(Y)21 = 0 (TN code = 0) and C(Y)20 = 1 an
                  // illegal procedure fault occurs.
                  if ((CN & 1) != 0)
                    doFault (cpu_p, FAULT_IPR, fst_ill_proc, "narn N9 and CN odd");
                  // The character number is in bits 18-19; recover it
                  CN >>= 1;
                  // If C(Y)21 = 0 (TN code = 0), then
                  //   C(Y)18,20 -> C(ARn.CHAR)
                  //   0000 -> C(ARn.BITNO)
                  SET_AR_CHAR_BITNO (n, (word2) CN, 0);
                  break;
              }
            HDBGRegAR (n);
          }
          break;

        /// EIS - Address Register Store

        // aran Address Register n to Alphanumeric Descriptor

                        // aarn
        case x1 (0540): // aar0
        case x1 (0541): // aar1
        case x1 (0542): // aar2
        case x1 (0543): // aar3
        case x1 (0544): // aar4
        case x1 (0545): // aar5
        case x1 (0546): // aar6
        case x1 (0547): // aar7
            {
                // The alphanumeric descriptor is fetched from Y and C(Y)21,22
                // (TA field) is examined to determine the data type described.
                PNL (L68_ (DU_CYCLE_DDU_STEA;))

                uint TA = getbits36_2 (cpu_p->CY, 21);

                // If C(Y)21,22 = 11 (TA code = 3) or C(Y)23 = 1 (unused bit),
                // an illegal procedure fault occurs.
                if (TA == 03)
                  doFault (cpu_p, FAULT_IPR,
                           fst_ill_proc,
                           "ARAn tag == 3");
                if (getbits36_1 (cpu_p->CY, 23) != 0)
                  doFault (cpu_p, FAULT_IPR,
                           fst_ill_proc,
                           "ARAn b23 == 1");

                uint32 n = opcode10 & 07;  // get
                CPTUR (cptUsePRn + n);
                // For n = 0, 1, ..., or 7 as determined by operation code

                // C(ARn.WORDNO) -> C(Y)0,17
                putbits36_18 (& cpu_p->CY, 0, cpu_p->AR[n].WORDNO & MASK18);

                // If TA = 1 (6-bit data) or TA = 2 (4-bit data), C(ARn.CHAR)
                // and C(ARn.BITNO) are translated to an equivalent character
                // position that goes to C(Y)18,20.

                int CN = 0;

                switch (TA)
                {
                    case CTA4:  // 2
                        // If C(Y)21,22 = 10 (TA code = 2), then
                        // (9 * C(ARn.CHAR) + C(ARn.BITNO) - 1) / 4 -> C(Y)18,20
                        CN = (9 * GET_AR_CHAR (n) + GET_AR_BITNO (n) - 1) / 4;
                        putbits36_3 (& cpu_p->CY, 18, (word3) CN & MASK3);
                        break;

                    case CTA6:  // 1
                        // If C(Y)21,22 = 01 (TA code = 1), then
                        // (9 * C(ARn.CHAR) + C(ARn.BITNO)) / 6 -> C(Y)18,20
                        CN = (9 * GET_AR_CHAR (n) + GET_AR_BITNO (n)) / 6;
                        putbits36_3 (& cpu_p->CY, 18, (word3) CN & MASK3);
                        break;

                    case CTA9:  // 0
                        // If C(Y)21,22 = 00 (TA code = 0), then
                        //   C(ARn.CHAR) -> C(Y)18,19
                        //   0 -> C(Y)20
                        putbits36_3 (& cpu_p->CY, 18,
                                     (word3) ((GET_AR_CHAR (n) & MASK2) << 1));
                        break;
                }
              cpu_p->zone = 0777777700000;
              cpu_p->useZone = true;
            }
            break;

        // arnn Address Register n to Numeric Descriptor 

                        // aarn
        case x1 (0640): // aar0
        case x1 (0641): // aar1
        case x1 (0642): // aar2
        case x1 (0643): // aar3
        case x1 (0644): // aar4
        case x1 (0645): // aar5
        case x1 (0646): // aar6
        case x1 (0647): // aar7
            {
                PNL (L68_ (DU_CYCLE_DDU_STEA;))
                uint32 n = opcode10 & 07;  // get register #
                CPTUR (cptUsePRn + n);

                // The Numeric descriptor is fetched from Y and C(Y)21,22 (TA
                // field) is examined to determine the data type described.

                uint TN = getbits36_1 (cpu_p->CY, 21); // C(Y) 21

                // For n = 0, 1, ..., or 7 as determined by operation code
                // C(ARn.WORDNO) -> C(Y)0,17
                putbits36_18 (& cpu_p->CY, 0, cpu_p->AR[n].WORDNO & MASK18);

                switch (TN)
                {
                    case CTN4:  // 1
                      {
                        // If C(Y)21 = 1 (TN code = 1) then
                        //   (9 * C(ARn.CHAR) + C(ARn.BITNO) - 1) / 4 ->
                        //     C(Y)18,20
                        word3 CN = (9 * GET_AR_CHAR (n) +
                                    GET_AR_BITNO (n) - 1) / 4;
                        putbits36_3 (& cpu_p->CY, 18, CN & MASK3);
                        break;
                      }
                    case CTN9:  // 0
                        // If C(Y)21 = 0 (TN code = 0), then
                        //   C(ARn.CHAR) -> C(Y)18,19
                        //   0 -> C(Y)20
                        putbits36_3 (& cpu_p->CY, 18,
                                     (word3) ((GET_AR_CHAR (n) & MASK2) << 1));
                        break;
                }
              cpu_p->zone = 0777777700000;
              cpu_p->useZone = true;
            }
            break;

        // sarn Store Address Register n

                        // sarn
        case x1 (0740): // sar0
        case x1 (0741): // sar1
        case x1 (0742): // sar2
        case x1 (0743): // sar3
        case x1 (0744): // sar4
        case x1 (0745): // sar5
        case x1 (0746): // sar6
        case x1 (0747): // sar7
            //For n = 0, 1, ..., or 7 as determined by operation code
            //  C(ARn) -> C(Y)0,23
            //  C(Y)24,35 -> unchanged
            {
                PNL (L68_ (DU_CYCLE_DDU_STEA;))
                uint32 n = opcode10 & 07;  // get n
                CPTUR (cptUsePRn + n);
                putbits36 (& cpu_p->CY,  0, 18, cpu_p->PR[n].WORDNO);
// AL-39 implies CHAR/BITNO, but ISOLTS test 805 requires BITNO
                putbits36 (& cpu_p->CY, 18, 2, GET_AR_CHAR (n));
                putbits36 (& cpu_p->CY, 20, 4, GET_AR_BITNO (n));
                //putbits36 (& cpu_p->CY, 18, 6, GET_PR_BITNO (n));
                cpu_p->zone = 0777777770000;
                cpu_p->useZone = true;
            }
#ifdef TEST_OLIN
          cmpxchg ();
#endif
          break;

        // sareg Store Address Registers 

        case x1 (0443):  // sareg
            // a:AL39/ar1 According to ISOLTS ps805, the BITNO data is stored
            // in BITNO format, not CHAR/BITNO.
            PNL (L68_ (DU_CYCLE_DDU_STEA;))
            memset (cpu_p->Yblock8, 0, sizeof (cpu_p->Yblock8));
            for (uint32 n = 0 ; n < 8 ; n += 1)
            {
                CPTUR (cptUsePRn + n);
                word36 arx = 0;
                putbits36 (& arx,  0, 18, cpu_p->PR[n].WORDNO);
                putbits36 (& arx, 18,  2, GET_AR_CHAR (n));
                putbits36 (& arx, 20,  4, GET_AR_BITNO (n));
                cpu_p->Yblock8[n] = arx;
            }
            break;

        // spl Store Pointers and Lengths

        case x1 (0447):  // spl
            PNL (L68_ (DU_CYCLE_DDU_STEA;))
            du2words (cpu_p, cpu_p->Yblock8);
          break;

        /// EIS - Address Register Special Arithmetic

        // a4bd Add 4-bit Displacement to Address Register 5

        case x1 (0502):  // a4bd
          asxbd (4, false);
          break;

        // a6bd Add 6-bit Displacement to Address Register

        case x1 (0501):  // a6bd
          asxbd (6, false);
          break;

        // a9bd Add 9-bit Displacement to Address Register 

        case x1 (0500):  // a9bd
          asxbd (9, false);
          break;

        // abd Add Bit Displacement to Address Register 

        case x1 (0503):  // abd
          asxbd (1, false);
          break;

        // awd Add Word Displacement to Address Register

        case x1 (0507):  // awd
          asxbd (36, false);
          break;

        // s4bd Subtract 4-bit Displacement from Address Register

        case x1 (0522):  // s4bd
          asxbd (4, true);
          break;

        // s6bd Subtract 6-bit Displacement from Address Register

        case x1 (0521):  // s6bd
          asxbd (6, true);
          break;

        // s9bd Subtract 9-bit Displacement from Address Register

        case x1 (0520):  // s9bd
          asxbd (9, true);
          break;

        // sbd Subtract Bit Displacement from Address Register

        case x1 (0523):  // sbd
          asxbd (1, true);
          break;

        // swd Subtract Word Displacement from Address Register

        case x1 (0527):  // swd
          asxbd (36, true);
          break;

        /// EIS = Alphanumeric Compare

        case x1 (0106):  // cmpc
          cmpc ();
          break;

        case x1 (0120):  // scd
          scd ();
          break;

        case x1 (0121):  // scdr
          scdr ();
          break;

        case x1 (0124):  // scm
          scm ();
          break;

        case x1 (0125):  // scmr
          scmr ();
          break;

        case x1 (0164):  // tct
          tct ();
          break;

        case x1 (0165):  // tctr
          tctr ();
          break;

        /// EIS - Alphanumeric Move

        case x1 (0100):  // mlr
          mlr ();
          break;

        case x1 (0101):  // mrl
          mrl ();
          break;

        case x1 (0020):  // mve
          mve ();
          break;

        case x1 (0160):  // mvt
          mvt ();
          break;

        /// EIS - Numeric Compare

        case x1 (0303):  // cmpn
          cmpn ();
          break;

        /// EIS - Numeric Move

        case x1 (0300):  // mvn
          mvn ();
          break;

        case x1 (0024):   // mvne
          mvne ();
          break;

        /// EIS - Bit String Combine

        case x1 (0060):   // csl
          csl (false);
          break;

        case x1 (0061):   // csr
          csr (false);
          break;

        /// EIS - Bit String Compare

        case x1 (0066):   // cmpb
          cmpb ();
          break;

        /// EIS - Bit String Set Indicators

        case x1 (0064):   // sztl
          // The execution of this instruction is identical to the Combine
          // Bit Strings Left (csl) instruction except that C(BOLR)m is
          // not placed into C(Y-bit2)i-1.
          csl (true);
          break;

        case x1 (0065):   // sztr
          // The execution of this instruction is identical to the Combine
          // Bit Strings Left (csr) instruction except that C(BOLR)m is
          // not placed into C(Y-bit2)i-1.
          csr (true);
          break;

        /// EIS -- Data Conversion

        case x1 (0301):  // btd
          btd ();
          break;

        case x1 (0305):  // dtb
          dtb ();
          break;

        /// EIS - Decimal Addition

        case x1 (0202):  // ad2d
            ad2d ();
            break;

        case x1 (0222):  // ad3d
            ad3d ();
            break;

        /// EIS - Decimal Subtraction

        case x1 (0203):  // sb2d
            sb2d ();
            break;

        case x1 (0223):  // sb3d
            sb3d ();
            break;

        /// EIS - Decimal Multiplication

        case x1 (0206):  // mp2d
            mp2d ();
            break;

        case x1 (0226):  // mp3d
            mp3d ();
            break;

        /// EIS - Decimal Division

        case x1 (0207):  // dv2d
            dv2d ();
            break;

        case x1 (0227):  // dv3d
            dv3d ();
            break;

#ifdef TESTING
#if EMULATOR_ONLY

        case x1 (0420):  // emcall instruction Custom, for an emulator call for
                    //  simh stuff ...
        {
            int ret = emCall ();
            if (ret)
              return ret;
            break;
        }
#endif
#endif

        default:
          if (cpu_p->switches.halt_on_unimp)
            return STOP_STOP;
          doFault (cpu_p, FAULT_IPR,
                   fst_ill_op,
                   "Illegal instruction");
      }
#ifdef L68
    cpu_p->ou.STR_OP = (is_ou && (i->info->flags & (STORE_OPERAND | STORE_YPAIR))) ? 1 : 0; 
    cpu_p->ou.cycle |= ou_GOF;
    if (cpu_p->MR_cache.emr && cpu_p->MR_cache.ihr && is_ou)
      add_OU_history ();
    if (cpu_p->MR_cache.emr && cpu_p->MR_cache.ihr && is_du)
      add_DU_history ();
#endif
    return SCPE_OK;
}



#ifdef TESTING
#include <ctype.h>

#if EMULATOR_ONLY
/**
 * emulator call instruction. Do whatever address field sez' ....
 */
static int emCall (cpu_state_t *cpu_p)
{
    DCDstruct * i = & cpu_p->currentInstruction;
    switch (i->address) // address field
    {
        case 1:     // putc9 - put 9-bit char in AL to stdout
        {
            if (cpu_p->rA > 0xff)  // don't want no 9-bit bytes here!
                break;

            char c = cpu_p->rA & 0x7f;
            if (c)  // ignore NULL chars.
                sim_printf ("%c", c);
            break;
        }
        case 0100:     // putc9 - put 9-bit char in A(0) to stdout
        {
            char c = (cpu_p->rA >> 27) & 0x7f;
            if (isascii (c))  // ignore NULL chars.
                sim_printf ("%c", c);
            else
                sim_printf ("\\%03o", c);
            break;
        }
        case 2:     // putc6 - put 6-bit char in A to stdout
        {
            int c = GEBcdToASCII[cpu_p->rA & 077];
            if (c != -1)
            {
                if (isascii (c))  // ignore NULL chars.
                    sim_printf ("%c", c);
                else
                    sim_printf ("\\%3o", c);
            }
            break;
        }
        case 3:     // putoct - put octal contents of A to stdout (split)
        {
            sim_printf ("%06o %06o", GETHI (cpu_p->rA), GETLO (cpu_p->rA));
            break;
        }
        case 4:     // putoctZ - put octal contents of A to stdout
                    // (zero-suppressed)
        {
            sim_printf ("%"PRIo64"", cpu_p->rA);
            break;
        }
        case 5:     // putdec - put decimal contents of A to stdout
        {
            t_int64 tmp = SIGNEXT36_64 (cpu_p->rA);
            sim_printf ("%"PRId64"", tmp);
            break;
        }
        case 6:     // putEAQ - put float contents of C(EAQ) to stdout
        {
#ifndef __MINGW64__
            long double eaq = EAQToIEEElongdouble ();
            sim_printf ("%12.8Lg", eaq);
#else
            double eaq = EAQToIEEEdouble();
            sim_printf("%12.8g", eaq);
#endif
            break;
        }
        case 7:   // dump index registers
            for (int i = 0 ; i < 8 ; i += 4)
                sim_printf ("r[%d]=%06o r[%d]=%06o r[%d]=%06o r[%d]=%06o\n",
                           i+0, cpu_p->rX[i+0], i+1, cpu_p->rX[i+1], i+2, cpu_p->rX[i+2],
                           i+3, cpu_p->rX[i+3]);
            break;

        case 17: // dump pointer registers
            for (int n = 0 ; n < 8 ; n++)
            {
                sim_printf ("PR[%d]/%s: SNR=%05o RNR=%o WORDNO=%06o "
                           "BITNO:%02o\n",
                           n, PRalias[n], cpu_p->PR[n].SNR, cpu_p->PR[n].RNR,
                           cpu_p->PR[n].WORDNO, GET_PR_BITNO (n));
            }
            break;
        case 27:    // dump registers A & Q
            sim_printf ("A: %012"PRIo64" Q:%012"PRIo64"\n", cpu_p->rA, cpu_p->rQ);
            break;

        case 8: // crlf to console
            sim_printf ("\n");
            break;

        case 13:     // putoct - put octal contents of Q to stdout (split)
        {
            sim_printf ("%06o %06o", GETHI (cpu_p->rQ), GETLO (cpu_p->rQ));
            break;
        }
        case 14:     // putoctZ - put octal contents of Q to stdout
                     // (zero-suppressed)
        {
            sim_printf ("%"PRIo64"", cpu_p->rQ);
            break;
        }
        case 15:     // putdec - put decimal contents of Q to stdout
        {
            t_int64 tmp = SIGNEXT36_64 (cpu_p->rQ);
            sim_printf ("%"PRId64"", tmp);
            break;
        }

        case 16:     // puts - A high points to by an aci string; print it.
                     // The string includes C-sytle escapes: \0 for end
                     // of string, \n for newline, \\ for a backslash
        case 21: // puts: A contains a 24 bit address
        {
            const int maxlen = 256;
            char buf[maxlen + 1];

            word36 addr;
            if (i->address == 16)
              addr = cpu_p->rA >> 18;
            else // 21
              addr = cpu_p->rA >> 12;
            word36 chunk = 0;
            int i;
            bool is_escape = false;
            int cnt = 0;

            for (i = 0; cnt < maxlen; i ++)
            {
                // fetch char
                if (i % 4 == 0)
                    chunk = M[addr ++];
                word36 wch = chunk >> (9 * 3);
                chunk = (chunk << 9) & DMASK;
                char ch = (char) (wch & 0x7f);

                if (is_escape)
                {
                    if (ch == '0')
                        ch = '\0';
                    else if (ch == 'n')
                        ch = '\n';
                    else
                    {
                        /* ch = ch */;
                    }
                    is_escape = false;
                    buf[cnt ++] = ch;
                    if (ch == '\0')
                      break;
                }
                else
                {
                    if (ch == '\\')
                        is_escape = true;
                    else
                    {
                        buf[cnt ++] = ch;
                        if (ch == '\0')
                            break;
                    }
                }
            }
            // Safety; if filled buffer before finding eos, put an eos
            // in the extra space that was allocated
            buf[maxlen] = '\0';
            sim_printf ("%s", buf);
            break;
        }

        // case 17 used above

        case 18:     // halt
            return STOP_STOP;

        case 19:     // putdecaq - put decimal contents of AQ to stdout
        {
            int64_t t0 = SIGNEXT36_64 (cpu_p->rA);
            __int128_t AQ = ((__int128_t) t0) << 36;
            AQ |= (cpu_p->rQ & DMASK);
            print_int128 (AQ, NULL);
            break;
        }

        case 20:    // Report fault
        {
            emCallReportFault ();
             break;
        }

        // case 21 defined above

    }
    return 0;
}
#endif
#endif // TESTING

// CANFAULT
static int doABSA (cpu_state_t *cpu_p, word36 * result)
  {
    word36 res;
    sim_debug (DBG_APPENDING, & cpu_dev, "absa CA:%08o\n", cpu_p->TPR.CA);

    //if (get_addr_mode () == ABSOLUTE_mode && ! cpu_p->isb29)
    //if (get_addr_mode () == ABSOLUTE_mode && ! cpu_p->went_appending) // ISOLTS-860
    if (get_addr_mode (cpu_p) == ABSOLUTE_mode && ! cpu_p->cu.XSF) // ISOLTS-860
      {
        * result = ((word36) (cpu_p->TPR.CA & MASK18)) << 12; // 24:12 format
        return SCPE_OK;
      }

    // ABSA handles directed faults differently, so a special append cycle is
    // needed.
    // do_append_cycle also provides WAM support, which is required by
    // ISOLTS-860 02
    //   res = (word36) do_append_cycle (cpu_p->TPR.CA & MASK18, ABSA_CYCLE, NULL,
    //                                   0) << 12;
    res = (word36) do_append_cycle (cpu_p, ABSA_CYCLE, NULL, 0) << 12;

    * result = res;

    return SCPE_OK;
  }

void doRCU (cpu_state_t *cpu_p)
  {
#ifdef LOOPTRC
elapsedtime ();
 sim_printf (" rcu to %05o:%06o  PSR:IC %05o:%06o\r\n",  (cpu_p->Yblock8[0]>>18)&MASK15, (cpu_p->Yblock8[4]>>18)&MASK18, cpu_p->PPR.PSR, cpu_p->PPR.IC);
#endif

    if_sim_debug (DBG_TRACEEXT, & cpu_dev)
      {
        for (int i = 0; i < 8; i ++)
          {
            sim_debug (DBG_TRACEEXT, & cpu_dev, "RCU %d %012"PRIo64"\n", i,
                       cpu_p->Yblock8[i]);
          }
      }

    words2scu (cpu_p, cpu_p->Yblock8);

// Restore addressing mode

    word1 saveP = cpu_p->PPR.P; // ISOLTS-870 02m
    if (TST_I_ABS == 0)
      set_addr_mode (cpu_p, APPEND_mode);
    else
      set_addr_mode (cpu_p, ABSOLUTE_mode);
    cpu_p->PPR.P = saveP;

    if (cpu_p->cu.FLT_INT == 0) // is interrupt, not fault
      {
        sim_debug (DBG_TRACEEXT, & cpu_dev, "RCU interrupt return\n");
        longjmp (cpu_p->jmpMain, JMP_REFETCH);
      }

    // Resync the append unit
    fauxDoAppendCycle (cpu_p, INSTRUCTION_FETCH);

// All of the faults list as having handlers have actually
// been encountered in Multics operation and are believed
// to be being handled correctly. The handlers in
// parenthesis are speculative and untested.
//
// Unhandled:
//
//    SDF Shutdown: Why would you RCU from a shutdown fault?
//    STR Store:
//      AL39 is contradictory or vague about store fault subfaults and store
//      faults in general. They are mentioned:
//        SPRPn: store fault (illegal pointer) (assuming STR:ISN)
//        SMCM: store fault (not control)  -
//        SMIC: store fault (not control)   > I believe that these should be
//        SSCR: store fault (not control)  -  command fault
//        TSS:  STR:OOB
//        Bar mode out-of-bounds: STR:OOB
//     The SCU register doesn't define which bit is "store fault (not control)"
// STR:ISN - illegal segment number
// STR:NEA - nonexistent address
// STR:OOB - bar mode out-of-bounds
//
// decimal   octal
// fault     fault  mnemonic   name             priority group  handler
// number   address
//   0         0      sdf      Shutdown               27 7
//   1         2      str      Store                  10 4                                  get_BAR_address, instruction execution
//   2         4      mme      Master mode entry 1    11 5      JMP_SYNC_FAULT_RETURN       instruction execution
//   3         6      f1       Fault tag 1            17 5      (JMP_REFETCH/JMP_RESTART)   do_caf
//   4        10      tro      Timer runout           26 7      JMP_REFETCH                 FETCH_cycle
//   5        12      cmd      Command                 9 4      JMP_REFETCH/JMP_RESTART     instruction execution
//   6        14      drl      Derail                 15 5      JMP_REFETCH/JMP_RESTART     instruction execution
//   7        16      luf      Lockup                  5 4      JMP_REFETCH                 do_caf, FETCH_cycle
//   8        20      con      Connect                25 7      JMP_REFETCH                 FETCH_cycle
//   9        22      par      Parity                  8 4
//  10        24      ipr      Illegal procedure      16 5                                  doITSITP, do_caf, instruction execution
//  11        26      onc      Operation not complete  4 2                                  nem_check, instruction execution
//  12        30      suf      Startup                 1 1
//  13        32      ofl      Overflow                7 3      JMP_REFETCH/JMP_RESTART     instruction execution
//  14        34      div      Divide check            6 3                                  instruction execution
//  15        36      exf      Execute                 2 1      JMP_REFETCH/JMP_RESTART     FETCH_cycle
//  16        40      df0      Directed fault 0       20 6      JMP_REFETCH/JMP_RESTART     getSDW, do_append_cycle
//  17        42      df1      Directed fault 1       21 6      JMP_REFETCH/JMP_RESTART     getSDW, do_append_cycle
//  18        44      df2      Directed fault 2       22 6      (JMP_REFETCH/JMP_RESTART)   getSDW, do_append_cycle
//  19        46      df3      Directed fault 3       23 6      JMP_REFETCH/JMP_RESTART     getSDW, do_append_cycle
//  20        50      acv      Access violation       24 6      JMP_REFETCH/JMP_RESTART     fetchDSPTW, modifyDSPTW, fetchNSDW, do_append_cycle, EXEC_cycle (ring alarm)
//  21        52      mme2     Master mode entry 2    12 5      JMP_SYNC_FAULT_RETURN       instruction execution
//  22        54      mme3     Master mode entry 3    13 5      (JMP_SYNC_FAULT_RETURN)     instruction execution
//  23        56      mme4     Master mode entry 4    14 5      (JMP_SYNC_FAULT_RETURN)     instruction execution
//  24        60      f2       Fault tag 2            18 5      JMP_REFETCH/JMP_RESTART     do_caf
//  25        62      f3       Fault tag 3            19 5      JMP_REFETCH/JMP_RESTART     do_caf
//  26        64               Unassigned
//  27        66               Unassigned
//  28        70               Unassigned
//  29        72               Unassigned
//  30        74               Unassigned
//  31        76      trb      Trouble                 3 2                                  FETCH_cycle, doRCU


// Reworking logic

#define rework
#ifdef rework
    if (cpu_p->cu.FIF) // fault occured during instruction fetch
      {
//if (cpu_p->cu.rfi) sim_printf ( "RCU FIF refetch return caught rfi\n");
        // I am misusing this bit; on restart I want a way to tell the
        // CPU state machine to restart the instruction, which is not
        // how Multics uses it. I need to pick a different way to
        // communicate; for now, turn it off on refetch so the state
        // machine doesn't become confused.
        cpu_p->cu.rfi = 0;
        sim_debug (DBG_TRACEEXT, & cpu_dev, "RCU FIF REFETCH return\n");
        longjmp (cpu_p->jmpMain, JMP_REFETCH);
      }

// RFI means 'refetch this instruction'
    if (cpu_p->cu.rfi)
      {
//sim_printf ( "RCU rfi refetch return\n");
        sim_debug (DBG_TRACEEXT, & cpu_dev, "RCU rfi refetch return\n");
// Setting the to RESTART causes ISOLTS 776 to report unexpected
// trouble faults.
// Without clearing rfi, ISOLTS pm776-08i LUFs.
        cpu_p->cu.rfi = 0;
        longjmp (cpu_p->jmpMain, JMP_REFETCH);
      }

// The debug command uses MME2 to implement breakpoints, but it is not
// clear what it does to the MC data to signal RFI behavior.

    if (cpu_p->cu.FI_ADDR == FAULT_MME ||
        cpu_p->cu.FI_ADDR == FAULT_MME2 ||
        cpu_p->cu.FI_ADDR == FAULT_MME3 ||
        cpu_p->cu.FI_ADDR == FAULT_MME4 ||
        cpu_p->cu.FI_ADDR == FAULT_DRL)
    //if (cpu_p->cu.FI_ADDR == FAULT_MME2)
      {
//sim_printf ("MME2 restart\n");
        sim_debug (DBG_TRACEEXT, & cpu_dev, "RCU MME2 restart return\n");
        cpu_p->cu.rfi = 0;
        longjmp (cpu_p->jmpMain, JMP_RESTART);
      }
#else
    if (cpu_p->cu.rfi || // S/W asked for the instruction to be started
        cpu_p->cu.FIF) // fault occured during instruction fetch
      {

        // I am misusing this bit; on restart I want a way to tell the
        // CPU state machine to restart the instruction, which is not
        // how Multics uses it. I need to pick a different way to
        // communicate; for now, turn it off on refetch so the state
        // machine doesn't become confused.

        cpu_p->cu.rfi = 0;
        sim_debug (DBG_TRACEEXT, & cpu_dev, "RCU rfi/FIF REFETCH return\n");
        longjmp (cpu_p->jmpMain, JMP_REFETCH);
      }

// It seems obvious that MMEx should do a JMP_SYNC_FAULT_RETURN, but doing
// a JMP_RESTART makes 'debug' work. (The same change to DRL does not make
// 'gtss' work, tho.

    if (cpu_p->cu.FI_ADDR == FAULT_MME2)
      {
//sim_printf ("MME2 restart\n");
        sim_debug (DBG_TRACEEXT, & cpu_dev, "RCU MME2 restart return\n");
        cpu_p->cu.rfi = 1;
        longjmp (cpu_p->jmpMain, JMP_RESTART);
      }
#endif

#if 0
// I beleive this logic is correct (cf. ISOLTS pa870 test-02d TRA PR1|6 not
// switching to append mode do to page fault clearing went_appending), but the
// emulator's refetching of operand descriptors after page fault of EIS
// instruction in absolute mode is breaking the logic.
    // If restarting after a page fault, set went_appending...
    if (cpu_p->cu.FI_ADDR == FAULT_DF0 ||
        cpu_p->cu.FI_ADDR == FAULT_DF1 ||
        cpu_p->cu.FI_ADDR == FAULT_DF2 ||
        cpu_p->cu.FI_ADDR == FAULT_DF3 ||
        cpu_p->cu.FI_ADDR == FAULT_ACV ||
        cpu_p->cu.FI_ADDR == FAULT_F1 ||
        cpu_p->cu.FI_ADDR == FAULT_F2 ||
        cpu_p->cu.FI_ADDR == FAULT_F3)
      {
        set_went_appending ();
      }
#endif
    // MME faults resume with the next instruction



#ifdef rework
    if (cpu_p->cu.FI_ADDR == FAULT_DIV ||
        cpu_p->cu.FI_ADDR == FAULT_OFL ||
        cpu_p->cu.FI_ADDR == FAULT_IPR)
      {
        sim_debug (DBG_TRACEEXT, & cpu_dev, "RCU sync fault return\n");
        cpu_p->cu.rfi = 0;
        longjmp (cpu_p->jmpMain, JMP_SYNC_FAULT_RETURN);
      }
#else
    if (cpu_p->cu.FI_ADDR == FAULT_MME ||
        /* cpu_p->cu.FI_ADDR == FAULT_MME2 || */
        cpu_p->cu.FI_ADDR == FAULT_MME3 ||
        cpu_p->cu.FI_ADDR == FAULT_MME4 ||
        cpu_p->cu.FI_ADDR == FAULT_DRL ||
        cpu_p->cu.FI_ADDR == FAULT_DIV ||
        cpu_p->cu.FI_ADDR == FAULT_OFL ||
        cpu_p->cu.FI_ADDR == FAULT_IPR)
      {
        sim_debug (DBG_TRACEEXT, & cpu_dev, "RCU MMEx sync fault return\n");
        cpu_p->cu.rfi = 0;
        longjmp (cpu_p->jmpMain, JMP_SYNC_FAULT_RETURN);
      }
#endif






    // LUF can happen during fetch or CAF. If fetch, handled above
    if (cpu_p->cu.FI_ADDR == FAULT_LUF)
      {
        cpu_p->cu.rfi = 1;
        sim_debug (DBG_TRACEEXT, & cpu_dev, "RCU LUF RESTART return\n");
        longjmp (cpu_p->jmpMain, JMP_RESTART);
      }

    if (cpu_p->cu.FI_ADDR == FAULT_DF0 ||
        cpu_p->cu.FI_ADDR == FAULT_DF1 ||
        cpu_p->cu.FI_ADDR == FAULT_DF2 ||
        cpu_p->cu.FI_ADDR == FAULT_DF3 ||
        cpu_p->cu.FI_ADDR == FAULT_ACV ||
        cpu_p->cu.FI_ADDR == FAULT_F1 ||
        cpu_p->cu.FI_ADDR == FAULT_F2 ||
        cpu_p->cu.FI_ADDR == FAULT_F3 ||
        cpu_p->cu.FI_ADDR == FAULT_CMD ||
        cpu_p->cu.FI_ADDR == FAULT_EXF)
      {
        // If the fault occurred during fetch, handled above.
        cpu_p->cu.rfi = 1;
        sim_debug (DBG_TRACEEXT, & cpu_dev, "RCU ACV RESTART return\n");
        longjmp (cpu_p->jmpMain, JMP_RESTART);
      }
    sim_printf ("doRCU dies with unhandled fault number %d\n", cpu_p->cu.FI_ADDR);
    doFault (cpu_p, FAULT_TRB,
             (_fault_subtype) {.bits=cpu_p->cu.FI_ADDR},
             "doRCU dies with unhandled fault number");
  }


