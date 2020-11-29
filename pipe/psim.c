/**************************************************************************
 * psim.c - Pipelined Y86-64 simulator
 * 
 * Copyright (c) 2010, 2015. Bryant and D. O'Hallaron, All rights reserved.
 * May not be used, modified, or copied without permission.
 **************************************************************************/

#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <unistd.h>
#include <string.h>

#include "isa.h"
#include "pipeline.h"
#include "stages.h"
#include "sim.h"

#define MAXBUF 1024
#define DEFAULTNAME "Y86-64 Simulator: "

#define MAXARGS 128
#define MAXBUF 1024
#define TKARGS 3

/***************
 * Begin Globals
 ***************/

/* Simulator name defined and initialized by the compiled HCL file */
/* according to the -n argument supplied to hcl2c */
char simname[] = "Y86-64 Processor: PIPE";

/* Parameters modifed by the command line */
char *object_filename;      /* The input object file name. */
FILE *object_file;          /* Input file handle */
bool_t verbosity = 2;       /* Verbosity level [TTY only] (-v) */
word_t instr_limit = 10000; /* Instruction limit [TTY only] (-l) */
bool_t do_check = FALSE;    /* Test with ISA simulator? [TTY only] (-t) */

/************* 
 * End Globals 
 *************/

/***************************
 * Begin function prototypes 
 ***************************/

word_t sim_run_pipe(word_t max_instr, word_t max_cycle, byte_t *statusp, cc_t *ccp);
static void usage(char *name); /* Print helpful usage message */
static void run_tty_sim();     /* Run simulator in TTY mode */

/*************************
 * End function prototypes
 *************************/

/*******************************************************************
 * Part 1: This part is the initial entry point that handles general
 * initialization. It parses the command line and does any necessary
 * setup to run in TTY mode, and then starts the
 * simulation.
 * Do not change any of these.
 *******************************************************************/

/* 
 * sim_main - main simulator routine. This function is called from the
 * main() routine in the HCL file.
 */
int sim_main(int argc, char **argv)
{
    int i;
    int c;

    /* Parse the command line arguments */
    while ((c = getopt(argc, argv, "htl:v:")) != -1)
    {
        switch (c)
        {
        case 'h':
            usage(argv[0]);
            break;
        case 'l':
            instr_limit = atoll(optarg);
            break;
        case 'v':
            verbosity = atoi(optarg);
            if (verbosity < 0 || verbosity > 2)
            {
                printf("Invalid verbosity %d\n", verbosity);
                usage(argv[0]);
            }
            break;
        case 't':
            do_check = TRUE;
            break;
        default:
            printf("Invalid option '%c'\n", c);
            usage(argv[0]);
            break;
        }
    }

    /* Do we have too many arguments? */
    if (optind < argc - 1)
    {
        printf("Too many command line arguments:");
        for (i = optind; i < argc; i++)
            printf(" %s", argv[i]);
        printf("\n");
        usage(argv[0]);
    }

    /* The single unflagged argument should be the object file name */
    object_filename = NULL;
    object_file = NULL;
    if (optind < argc)
    {
        object_filename = argv[optind];
        object_file = fopen(object_filename, "r");
        if (!object_file)
        {
            fprintf(stderr, "Couldn't open object file %s\n", object_filename);
            exit(1);
        }
    }

    /* Otherwise, run the simulator in TTY mode (no -g flag) */
    run_tty_sim();

    exit(0);
}

int main(int argc, char *argv[]) { return sim_main(argc, argv); }

/* 
 * run_tty_sim - Run the simulator in TTY mode
 */
static void run_tty_sim()
{
    word_t icount = 0;
    byte_t run_status = STAT_AOK;
    cc_t result_cc = 0;
    word_t byte_cnt = 0;
    mem_t mem0, reg0;
    state_ptr isa_state = NULL;

    /* In TTY mode, the default object file comes from stdin */
    if (!object_file)
    {
        object_file = stdin;
    }

    if (verbosity >= 2)
        sim_set_dumpfile(stdout);
    sim_init();

    /* Emit simulator name */
    if (verbosity >= 2)
        printf("%s\n", simname);

    byte_cnt = load_mem(mem, object_file, 1);
    if (byte_cnt == 0)
    {
        fprintf(stderr, "No lines of code found\n");
        exit(1);
    }
    else if (verbosity >= 2)
    {
        printf("%lld bytes of code read\n", byte_cnt);
    }
    fclose(object_file);
    if (do_check)
    {
        isa_state = new_state(0);
        free_mem(isa_state->r);
        free_mem(isa_state->m);
        isa_state->m = copy_mem(mem);
        isa_state->r = copy_mem(reg);
        isa_state->cc = cc;
    }

    mem0 = copy_mem(mem);
    reg0 = copy_mem(reg);

    icount = sim_run_pipe(instr_limit, 5 * instr_limit, &run_status, &result_cc);
    if (verbosity > 0)
    {
        printf("%lld instructions executed\n", icount);
        printf("Status = %s\n", stat_name(run_status));
        printf("Condition Codes: %s\n", cc_name(result_cc));
        printf("Changed Register State:\n");
        diff_reg(reg0, reg, stdout);
        printf("Changed Memory State:\n");
        diff_mem(mem0, mem, stdout);
    }
    if (do_check)
    {
        byte_t e = STAT_AOK;
        word_t step;
        bool_t match = TRUE;

        for (step = 0; step < instr_limit && e == STAT_AOK; step++)
        {
            e = step_state(isa_state, stdout);
        }

        if (diff_reg(isa_state->r, reg, NULL))
        {
            match = FALSE;
            if (verbosity > 0)
            {
                printf("ISA Register != Pipeline Register File\n");
                diff_reg(isa_state->r, reg, stdout);
            }
        }
        if (diff_mem(isa_state->m, mem, NULL))
        {
            match = FALSE;
            if (verbosity > 0)
            {
                printf("ISA Memory != Pipeline Memory\n");
                diff_mem(isa_state->m, mem, stdout);
            }
        }
        if (isa_state->cc != result_cc)
        {
            match = FALSE;
            if (verbosity > 0)
            {
                printf("ISA Cond. Codes (%s) != Pipeline Cond. Codes (%s)\n",
                       cc_name(isa_state->cc), cc_name(result_cc));
            }
        }
        if (match)
        {
            printf("ISA Check Succeeds\n");
        }
        else
        {
            printf("ISA Check Fails\n");
        }
    }

    /* Emit CPI statistics */
    {
        double cpi = instructions > 0 ? (double)cycles / instructions : 1.0;
        printf("CPI: %lld cycles/%lld instructions = %.2f\n",
               cycles, instructions, cpi);
    }
}

/*
 * usage - print helpful diagnostic information
 */
static void usage(char *name)
{
    printf("Usage: %s [-htg] [-l m] [-v n] file.yo\n", name);
    printf("   -h     Print this message\n");
    printf("   -l m   Set instruction limit to m [TTY mode only] (default %lld)\n", instr_limit);
    printf("   -v n   Set verbosity level to 0 <= n <= 2 [TTY mode only] (default %d)\n", verbosity);
    printf("   -t     Test result against ISA simulator [TTY mode only]\n");
    exit(0);
}

/*********************************************************
 * Part 2: This part contains the core simulator routines.
 * You only need to modify function sim_step_pipe()
 *********************************************************/

/*****************
 *  Part 2 Globals
 *****************/

/* Performance monitoring */
/* How many cycles have been simulated? */
word_t cycles = 0;
/* How many instructions have passed through the WB stage? */
word_t instructions = 0;

/* Has simulator gotten past initial bubbles? */
static int starting_up = 1;

/* Both instruction and data memory */
mem_t mem;
word_t minAddr = 0;
word_t memCnt = 0;

/* Register file */
mem_t reg;
/* Condition code register */
cc_t cc;
/* Status code */
stat_t status;

/* Pending updates to state */
word_t cc_in = DEFAULT_CC;
word_t wb_destE = REG_NONE;
word_t wb_valE = 0;
word_t wb_destM = REG_NONE;
word_t wb_valM = 0;
word_t mem_addr = 0;
word_t mem_data = 0;
bool_t mem_write = FALSE;

/* EX Operand sources */
mux_source_t amux = MUX_NONE;
mux_source_t bmux = MUX_NONE;

/* Current and next states of all pipeline registers */
pc_ptr pc_curr;
if_id_ptr if_id_curr;
id_ex_ptr id_ex_curr;
ex_mem_ptr ex_mem_curr;
mem_wb_ptr mem_wb_curr;

pc_ptr pc_next;
if_id_ptr if_id_next;
id_ex_ptr id_ex_next;
ex_mem_ptr ex_mem_next;
mem_wb_ptr mem_wb_next;

/* Intermediate values */
word_t f_pc;
byte_t imem_icode;
byte_t imem_ifun;
bool_t imem_error;
bool_t instr_valid;
word_t d_regvala;
word_t d_regvalb;
word_t e_vala;
word_t e_valb;
bool_t e_bcond;
bool_t dmem_error;

/* The pipeline state */
pipe_ptr pc_state, if_id_state, id_ex_state, ex_mem_state, mem_wb_state;

/* Simulator operating mode */
sim_mode_t sim_mode = S_FORWARD;
/* Log file */
FILE *dumpfile = NULL;

/*****************************************************************************
 * pipeline control
 * These functions can be used to handle hazards
 *****************************************************************************/

/* bubble stage (has effect at next update) */
void sim_bubble_stage(stage_id_t stage)
{
    switch (stage)
    {
    case IF_STAGE:
        pc_state->op = P_BUBBLE;
        break;
    case ID_STAGE:
        if_id_state->op = P_BUBBLE;
        break;
    case EX_STAGE:
        id_ex_state->op = P_BUBBLE;
        break;
    case MEM_STAGE:
        ex_mem_state->op = P_BUBBLE;
        break;
    case WB_STAGE:
        mem_wb_state->op = P_BUBBLE;
        break;
    }
}

/* stall stage (has effect at next update) */
void sim_stall_stage(stage_id_t stage)
{
    switch (stage)
    {
    case IF_STAGE:
        pc_state->op = P_STALL;
        break;
    case ID_STAGE:
        if_id_state->op = P_STALL;
        break;
    case EX_STAGE:
        id_ex_state->op = P_STALL;
        break;
    case MEM_STAGE:
        ex_mem_state->op = P_STALL;
        break;
    case WB_STAGE:
        mem_wb_state->op = P_STALL;
        break;
    }
}

static int initialized = 0;

void sim_init()
{
    /* Create memory and register files */
    initialized = 1;
    mem = init_mem(MEM_SIZE);
    reg = init_reg();

    /* create 5 pipe registers */
    pc_state = new_pipe(sizeof(pc_ele), (void *)&bubble_pc);
    if_id_state = new_pipe(sizeof(if_id_ele), (void *)&bubble_if_id);
    id_ex_state = new_pipe(sizeof(id_ex_ele), (void *)&bubble_id_ex);
    ex_mem_state = new_pipe(sizeof(ex_mem_ele), (void *)&bubble_ex_mem);
    mem_wb_state = new_pipe(sizeof(mem_wb_ele), (void *)&bubble_mem_wb);

    /* connect them to the pipeline stages */
    pc_next = pc_state->next;
    pc_curr = pc_state->current;

    if_id_next = if_id_state->next;
    if_id_curr = if_id_state->current;

    id_ex_next = id_ex_state->next;
    id_ex_curr = id_ex_state->current;

    ex_mem_next = ex_mem_state->next;
    ex_mem_curr = ex_mem_state->current;

    mem_wb_next = mem_wb_state->next;
    mem_wb_curr = mem_wb_state->current;

    sim_reset();
    clear_mem(mem);
}

void sim_reset()
{
    if (!initialized)
        sim_init();
    clear_pipes();
    clear_mem(reg);
    minAddr = 0;
    memCnt = 0;
    starting_up = 1;
    cycles = instructions = 0;
    cc = DEFAULT_CC;
    status = STAT_AOK;

    amux = bmux = MUX_NONE;
    cc = cc_in = DEFAULT_CC;
    wb_destE = REG_NONE;
    wb_valE = 0;
    wb_destM = REG_NONE;
    wb_valM = 0;
    mem_addr = 0;
    mem_data = 0;
    mem_write = FALSE;
}

/* Text representation of status */
void tty_report(word_t cyc)
{
    sim_log("\nCycle %lld. CC=%s, Stat=%s\n", cyc, cc_name(cc), stat_name(status));

    sim_log("F: predPC = 0x%llx\n", pc_curr->pc);

    sim_log("D: instr = %s, rA = %s, rB = %s, valC = 0x%llx, valP = 0x%llx, Stat = %s\n",
            iname(HPACK(if_id_curr->icode, if_id_curr->ifun)),
            reg_name(if_id_curr->ra), reg_name(if_id_curr->rb),
            if_id_curr->valc, if_id_curr->valp,
            stat_name(if_id_curr->status));

    sim_log("E: instr = %s, valC = 0x%llx, valA = 0x%llx, valB = 0x%llx\n   srcA = %s, srcB = %s, dstE = %s, dstM = %s, Stat = %s\n",
            iname(HPACK(id_ex_curr->icode, id_ex_curr->ifun)),
            id_ex_curr->valc, id_ex_curr->vala, id_ex_curr->valb,
            reg_name(id_ex_curr->srca), reg_name(id_ex_curr->srcb),
            reg_name(id_ex_curr->deste), reg_name(id_ex_curr->destm),
            stat_name(id_ex_curr->status));

    sim_log("M: instr = %s, Cnd = %d, valE = 0x%llx, valA = 0x%llx\n   dstE = %s, dstM = %s, Stat = %s\n",
            iname(HPACK(ex_mem_curr->icode, ex_mem_curr->ifun)),
            ex_mem_curr->takebranch,
            ex_mem_curr->vale, ex_mem_curr->vala,
            reg_name(ex_mem_curr->deste), reg_name(ex_mem_curr->destm),
            stat_name(ex_mem_curr->status));

    sim_log("W: instr = %s, valE = 0x%llx, valM = 0x%llx, dstE = %s, dstM = %s, Stat = %s\n",
            iname(HPACK(mem_wb_curr->icode, mem_wb_curr->ifun)),
            mem_wb_curr->vale, mem_wb_curr->valm,
            reg_name(mem_wb_curr->deste), reg_name(mem_wb_curr->destm),
            stat_name(mem_wb_curr->status));
}

/******************************************************************
 * This is the only function you need to modify for PIPE simulator.
 * It runs the pipeline for one cycle. max_instr indicates maximum 
 * number of instructions that want to complete during this 
 * simulation run.
 * You should update intermediate values for each stage, update 
 * global state values after all stages, and finally return the 
 * correct state.
 ******************************************************************/

/* Run pipeline for one cycle */
/* Return status of processor */
/* Max_instr indicates maximum number of instructions that
   want to complete during this simulation run.  */
static byte_t sim_step_pipe(word_t max_instr, word_t ccount)
{
    /* Update pipe registers */
    update_pipes();
    /* print status report in TTY mode */
    tty_report(ccount);
    /* error checking */
    if (pc_state->op == P_ERROR)
        pc_curr->status = STAT_PIP;
    if (if_id_state->op == P_ERROR)
        if_id_curr->status = STAT_PIP;
    if (id_ex_state->op == P_ERROR)
        id_ex_curr->status = STAT_PIP;
    if (ex_mem_state->op == P_ERROR)
        ex_mem_curr->status = STAT_PIP;
    if (mem_wb_state->op == P_ERROR)
        mem_wb_curr->status = STAT_PIP;

    /****************** Stage implementations ******************
     * TODO: implement the following functions to simulate the 
     * executations in each stage. 
     * You should also implement stalling, forwarding and branch 
     * prediction to handle data hazards and control hazards.
     * 
     * Since C code is executed sequencially, you need to do 
     * decode stage after execute & memory stages, and memory 
     * stage before execute, in order to propagate forwarding
     * values properly.
     ***********************************************************/

    do_wb_stage();
    do_mem_stage();
    do_ex_stage();
    do_id_stage();
    do_if_stage();
    do_stall_check();
    void next_vala();
    void next_valb();
    bool_t set_CC_Val();
    bool_t pipe_cntl_F_Stall();
    bool_t pipe_cntl_F_Bubble();
    bool_t pipe_cntl_D_Stall();
    bool_t pipe_cntl_D_Bubble();
    bool_t pipe_cntl_E_Stall();
    bool_t pipe_cntl_E_Bubble();
    bool_t pipe_cntl_M_Stall();
    bool_t pipe_cntl_M_Bubble();
    bool_t pipe_cntl_W_Stall();
    bool_t pipe_cntl_W_Bubble();

    /* Performance monitoring. Do not change anything below */
    if (mem_wb_curr->status != STAT_BUB && mem_wb_curr->icode != I_POP2)
    {
        starting_up = 0;
        instructions++;
        cycles++;
    }
    else
    {
        if (!starting_up)
            cycles++;
    }

    return status;
}

/*************************** Fetch stage ***************************
 * TODO: update [*if_id_next, f_pc]
 * you may find these functions useful: 
 * HPACK(), get_byte_val(), get_word_val(), HI4(), LO4()
 * 
 * imem_error is defined for logging purpose, you can use it to help
 * with your design, but it's also fine to neglect it 
 *******************************************************************/
void do_if_stage()
{

    // word_t valC = 0; 
    // byte_t instr = HPACK(I_NOP, F_NONE);
    // byte_t reg_ID = HPACK(REG_NONE, REG_NONE);

    // if(mem_wb_curr->icode == I_RET){
    //      f_pc = mem_wb_curr->valm;
    // }else if(ex_mem_curr->icode == I_JMP && !ex_mem_curr->takebranch){
    //     f_pc = ex_mem_curr->vala;
    // }else{
    //     f_pc = pc_curr->pc;
    // }
    // word_t valP = f_pc;
    // imem_error = !get_byte_val(mem, valP, &instr);
    // imem_icode = HI4(instr); imem_ifun = LO4(instr);
    
    // if_id_next->ifun = imem_error ? F_NONE : imem_ifun;
    // if_id_next->icode = imem_error ? I_NOP : imem_icode;

    // if(if_id_next->icode == I_ALU || if_id_next->icode == I_JMP || if_id_next->icode == I_NOP || if_id_next->icode == I_HALT || if_id_next->icode == I_RRMOVQ || if_id_next->icode == I_IRMOVQ || if_id_next->icode == I_RMMOVQ || if_id_next->icode == I_MRMOVQ 
    //     || if_id_next->icode == I_PUSHQ || if_id_next->icode == I_POPQ || if_id_next->icode == I_CALL || if_id_next->icode == I_RET){
    //     instr_valid = 1;
    // }else{
    //     instr_valid = 0;
    // }


    // if(!instr_valid){
    //     if_id_next->status = STAT_INS;
    // }else if(imem_error){
    //     if_id_next->status = STAT_ADR;
    // }else if (if_id_next->icode == I_HALT){
    //     if_id_next->status = STAT_HLT;
    // }else{
    //     if_id_next->status = STAT_AOK;
    // }

    // valP++;

    // if (if_id_next->icode == I_IRMOVQ || if_id_next->icode == I_RMMOVQ || if_id_next->icode == I_PUSHQ || if_id_next->icode == I_POPQ ||
    //     if_id_next->icode == I_RRMOVQ || if_id_next->icode == I_ALU || if_id_next->icode == I_MRMOVQ){
    //     get_byte_val(mem, valP, &reg_ID);
    //     valP++;
    // }

    // if_id_next->ra = HI4(reg_ID);
    // if_id_next->rb = LO4(reg_ID);


    // if (if_id_next->icode == I_IRMOVQ || if_id_next->icode == I_RMMOVQ || if_id_next->icode == I_MRMOVQ || if_id_next->icode == I_JMP || if_id_next->icode == I_CALL){
    //     get_word_val(mem, valP, &valC);
    //     valP += 8;
    // }
    // if_id_next->valp = valP;
    // if_id_next->valc = valC; 

    // if (if_id_next->icode == I_JMP || if_id_next->icode == I_CALL){
    //     pc_next->pc = if_id_next->valc;
    // }else{ 
    //     pc_next->pc = if_id_next->valp;
    // }

    // if(if_id_next->status == STAT_AOK){
    //     pc_next->status = STAT_AOK;
    // }else{
    //     pc_next->status = STAT_BUB;
    // }
    // if_id_next->stage_pc = f_pc;

    
    // /* logging function, do not change this */
    // if (!imem_error) {
    //     sim_log("\tFetch: f_pc = 0x%llx, f_instr = %s\n",
    //         f_pc, iname(HPACK(if_id_next->icode, if_id_next->ifun)));
    // }











   
    byte_t instr = HPACK(I_NOP, F_NONE);
    byte_t reg_ids;
    word_t valc = 0;
    word_t valp;
    if((ex_mem_curr->icode) == ((I_JMP) && !(ex_mem_curr -> takebranch))){
        if_id_next -> valp = ex_mem_curr -> vala;
    }else if(mem_wb_curr->icode == I_RET){
        if_id_next -> valp = mem_wb_curr->valm;
    }else{
        if_id_next -> valp = pc_curr -> pc;
    }
    imem_error = !get_byte_val(mem, f_pc, &instr);
        imem_icode = HI4(instr);
    imem_ifun = LO4(instr);
    if(imem_error){
        if_id_next -> icode = I_NOP;
        if_id_next -> ifun = F_NONE;
    }else{
        if_id_next -> icode = imem_ifun;
        if_id_next -> ifun =  imem_ifun;
    }
    if(imem_error){
        if_id_next->status = STAT_ADR;
    }else if(!instr_valid){
        if_id_next->status = STAT_INS;
    }else if (if_id_next->icode == I_HALT){
        if_id_next->status = STAT_HLT;
    }else{
        if_id_next->status = STAT_AOK;
    }
    instr_valid = (if_id_next -> icode >= I_HALT && if_id_next -> icode <= I_POP2);
    switch(imem_icode) {
        case I_HALT: 
            valp++;
            break;

        case I_NOP: 
            valp++;
            break;

        case I_RRMOVQ: 
            dmem_error |= !get_byte_val(mem, f_pc + 1, &reg_ids);
            if_id_next -> ra = HI4(reg_ids);
            if_id_next -> rb = LO4(reg_ids);
            valp += 2;
            break;

        case I_IRMOVQ: 
            dmem_error |= !get_byte_val(mem, valp + 1, &reg_ids);
            if_id_next -> ra = LO4(reg_ids);
            dmem_error |= !get_word_val(mem, valp + 2, &(valc));
            valp += 10;
            break;

        case I_RMMOVQ:
            dmem_error |= !get_byte_val(mem, valp + 1, &reg_ids);
            if_id_next -> ra = HI4(reg_ids);
            if_id_next -> rb = LO4(reg_ids);
            dmem_error |= !get_word_val(mem, valp + 2, &(valc));
            valp += 10;
            break;

        case I_MRMOVQ: 
        	dmem_error |= !get_byte_val(mem, valp + 1, &reg_ids);
            if_id_next -> ra = HI4(reg_ids);
            if_id_next -> rb = LO4(reg_ids);
            dmem_error |= !get_word_val(mem, valp + 2, &(valc));
            valp += 10;
            break;
   
        case I_ALU: 
            dmem_error |= !get_byte_val(mem, valp + 1, &reg_ids);
            if_id_next -> ra = HI4(reg_ids);
            if_id_next -> rb = LO4(reg_ids);
            valp += 2;
            break;
   
        case I_JMP:
            dmem_error |= !get_word_val(mem, valp + 1, &(valc));
            valp += 9;
            break;
        
        case I_CALL:
            dmem_error |= !get_word_val(mem, valp + 1, &(valc));
            valp += 9;
            break;
            
        case I_RET:
            valp++;
			break;

        case I_PUSHQ: 
            dmem_error |= !get_byte_val(mem, valp + 1, &reg_ids);
            if_id_next -> ra = HI4(reg_ids);
            if_id_next -> rb = LO4(reg_ids);
            valp += 2;
            break;

        case I_POPQ: 
            dmem_error |= !get_byte_val(mem, valp + 1, &reg_ids);
            if_id_next -> ra = HI4(reg_ids);
            if_id_next -> rb = LO4(reg_ids);
            valp += 2;
            break;

        default:
            imem_error = FALSE;
			printf("Invalid instruction\n");
			break;
    }
    
    if (if_id_next->icode == I_JMP || if_id_next->icode == I_CALL){
        pc_next->pc = if_id_next->valc;
    }else{ 
        pc_next->pc = if_id_next->valp;
    }

    if(if_id_next->status == STAT_AOK){
        pc_next->status = STAT_AOK;
    }else{
        pc_next->status = STAT_BUB;
    }

    if (!imem_error) {
        sim_log("\tFetch: f_pc = 0x%llx, f_instr = %s\n",
            f_pc, iname(HPACK(if_id_next->icode, if_id_next->ifun)));
    }
}
         

//     // if (!imem_error) {
//     //   byte_t junk;
//     //   /* Make sure can read maximum length instruction */
//     //   imem_error = !get_byte_val(mem, if_id_next -> valp + 5, &junk);
//     // }

//     instr_valid = TRUE;
//     
//     byte_t tempB;
//     if_id_next -> ra = REG_NONE;
//     if_id_next -> rb = REG_NONE;
//     
//     // pc_next->status = (if_id_next->status == STAT_AOK) ? STAT_AOK : STAT_BUB;
//     if(dmem_error){
//         if_id_next-> status = STAT_INS;
//     }       
//     /* logging function, do not change this */
//     if (!imem_error) {
//         sim_log("\tFetch: f_pc = 0x%llx, f_instr = %s\n",
//             f_pc, iname(HPACK(if_id_next->icode, if_id_next->ifun)));
//     }else if(imem_error){
//         if_id_next -> status = STAT_ADR;
//     }
//     if(!instr_valid){
//         if_id_next -> status = STAT_INS; 
//     }

//     if(if_id_next -> icode == I_JMP || if_id_next -> icode == I_CALL){
//         pc_next -> pc = if_id_next -> valc;
//     }else{
//         pc_next -> pc = if_id_next -> valp;
//     }
// }

void next_vala(){
        if(if_id_curr -> icode == I_CALL || if_id_curr -> icode == I_JMP){
            id_ex_next -> vala = if_id_curr -> valp;
        }
        if(id_ex_next -> srca == ex_mem_next -> deste){
            id_ex_next -> vala = ex_mem_next -> vale;
        }else if(id_ex_next -> srca == ex_mem_curr -> destm){
            id_ex_next -> vala = mem_wb_next -> valm; // mem_wb_curr -> valm
        }else if(id_ex_next -> srca == ex_mem_curr -> deste){
            id_ex_next -> vala = ex_mem_curr -> vale;
        }else if(id_ex_next -> srca == mem_wb_curr -> destm){
            id_ex_next -> vala = mem_wb_curr -> valm;
        }else if(id_ex_next -> srca == mem_wb_curr -> deste){
            id_ex_next -> vala = mem_wb_curr -> vale;
        }else{
            id_ex_next ->vala = get_reg_val(reg, id_ex_next -> srca);
        }
}

void next_valb(){
        if(id_ex_next -> srcb == ex_mem_next -> deste){
            id_ex_next -> valb = ex_mem_next -> vale;
        }else if(id_ex_next -> srcb == ex_mem_curr -> destm){
            id_ex_next -> valb = mem_wb_next -> valm;// mem_web_curr
        }else if(id_ex_next -> srcb == ex_mem_curr -> deste){
            id_ex_next -> valb = ex_mem_curr -> vale;
        }else if(id_ex_next -> srcb == mem_wb_curr -> destm){
            id_ex_next -> valb = mem_wb_curr -> valm;
        }else if(id_ex_next -> srcb == mem_wb_curr -> deste){
            id_ex_next -> valb = mem_wb_curr -> vale;
        }else{
            id_ex_next -> valb = get_reg_val(reg, id_ex_next -> srcb);
        }
}

/*************************** Decode stage ***************************
 * TODO: update [*id_ex_next]
 * you may find these functions useful:
 * get_reg_val()
 *******************************************************************/
void do_id_stage()
{
    id_ex_next -> srca = REG_NONE;
    id_ex_next -> srcb = REG_NONE;
    id_ex_next -> deste = REG_NONE;
    id_ex_next -> destm = REG_NONE;
    id_ex_next -> vala = 0;
    id_ex_next -> valb = 0;
		switch (if_id_curr -> icode) {
			case I_HALT: break;

			case I_NOP: break;
		
			case I_RRMOVQ: // aka CMOVQ
				id_ex_next -> srca = if_id_curr -> ra;
				id_ex_next -> deste = if_id_curr -> rb;
				break;

			case I_IRMOVQ:
				id_ex_next -> deste = if_id_curr -> rb;
                id_ex_next -> valc = if_id_curr -> valc;
				break;
				
			case I_RMMOVQ:
				id_ex_next -> srca = if_id_curr -> ra;
				id_ex_next -> srcb = if_id_curr -> rb;
                id_ex_next -> valc = if_id_curr -> valc;
				break;
				
			case I_MRMOVQ:
				id_ex_next -> srcb = if_id_curr -> rb;
				id_ex_next -> destm = if_id_curr -> ra;
                id_ex_next -> valc = if_id_curr -> valc;
				break;

			case I_ALU:
				id_ex_next -> srca = if_id_curr -> ra;
				id_ex_next -> srcb = if_id_curr -> rb;
				id_ex_next -> deste = if_id_curr -> rb;
				break;

			case I_JMP: 
            id_ex_next -> valc = if_id_curr -> valc;
            break;

			case I_CALL:
				id_ex_next -> srcb = REG_RSP;
				id_ex_next -> deste = REG_RSP;
                id_ex_next -> valc = if_id_curr -> valc;
				break;
				
			case I_RET:
				id_ex_next -> srca = REG_RSP;
				id_ex_next -> srcb = REG_RSP;
				id_ex_next -> deste = REG_RSP;
				break;

			case I_PUSHQ:
				id_ex_next -> srca = if_id_curr -> ra;
				id_ex_next -> srcb = REG_RSP;
				id_ex_next -> deste = REG_RSP;
				break;
				
			case I_POPQ:
				id_ex_next -> srca = REG_RSP;
				id_ex_next -> srcb = REG_RSP;
				id_ex_next -> deste = REG_RSP;
				id_ex_next -> destm = if_id_curr -> ra;
				break;
 
			default:
				printf("icode is not valid (%d)", if_id_curr -> icode);
				break;
		}
    next_vala();
    next_valb();
    id_ex_next->icode = if_id_curr->icode;
    id_ex_next->ifun = if_id_curr->ifun;
    id_ex_next->status = if_id_curr->status;
}

bool_t set_CC_Val(){
    bool_t m_stat = (mem_wb_next -> status == STAT_HLT || mem_wb_next -> status == STAT_ADR
        || mem_wb_next -> status == STAT_INS);
    bool_t w_stat = (mem_wb_curr -> status == STAT_HLT || mem_wb_curr -> status == STAT_ADR
        || mem_wb_curr -> status == STAT_INS);
    return !m_stat && !w_stat; 
}

/************************** Execute stage **************************
 * TODO: update [*ex_mem_next, cc_in]
 * you may find these functions useful: 
 * cond_holds(), compute_alu(), compute_cc()
 *******************************************************************/
void do_ex_stage()
{
    /* dummy placeholders, replace them with your implementation */
    cc_in = DEFAULT_CC; /* should not overwrite original cc */
    /* some useful variables for logging purpose */
    bool_t setcc = FALSE;
    alu_t alufun = A_NONE;
    word_t alua, alub;
    alua = alub = 0;
    /* logging functions, do not change these */
    if (id_ex_curr->icode == I_JMP)
    {
        sim_log("\tExecute: instr = %s, cc = %s, branch %staken\n",
                iname(HPACK(id_ex_curr->icode, id_ex_curr->ifun)),
                cc_name(cc),
                ex_mem_next->takebranch ? "" : "not ");
    }
    sim_log("\tExecute: ALU: %c 0x%llx 0x%llx --> 0x%llx\n",
            op_name(alufun), alua, alub, ex_mem_next->vale);
    if (setcc)
    {
        cc = cc_in;
        sim_log("\tExecute: New cc=%s\n", cc_name(cc_in));
    }

    ex_mem_next -> vale = 0;
    cc_in = cc;

    e_vala = id_ex_curr -> vala;
    e_valb = id_ex_curr -> valb;
    e_bcond = FALSE;
    ex_mem_next -> vala = e_vala;
		switch (id_ex_curr -> icode) {
			case I_HALT: break;

			case I_NOP: break;
		
			case I_RRMOVQ: // aka CMOVQ
				ex_mem_next -> vale = e_vala;
                e_bcond = cond_holds(cc_in, id_ex_curr -> ifun);
				break;

			case I_IRMOVQ:
				ex_mem_next -> vale = id_ex_curr -> valc;
				break;
				
			case I_RMMOVQ:
				ex_mem_next -> vale = e_valb + id_ex_curr -> valc;
				break;
				
			case I_MRMOVQ:
				ex_mem_next -> vale = e_valb + e_vala;
				break;

			case I_ALU:
				ex_mem_next -> vale = compute_alu(id_ex_curr -> ifun, e_vala, e_valb);
				cc_in = compute_cc(id_ex_curr -> ifun, e_vala, e_valb);
                setcc = set_CC_Val();
				break;

			case I_JMP:
				e_bcond = cond_holds(cc_in, id_ex_curr -> ifun);
				break;

			case I_CALL:
				ex_mem_next -> vale = e_valb - 8;
				break;
				
			case I_RET:
				ex_mem_next -> vale = e_valb + 8;
				break;

			case I_PUSHQ:
				ex_mem_next -> vale = e_valb - 8;
				break;
				
			case I_POPQ:
				ex_mem_next -> vale = e_valb + 8;
				break;

			default:
				printf("icode is not valid (%d)", ex_mem_next -> icode);
				break;
    }
    ex_mem_next -> vala = e_vala;
    ex_mem_next -> ifun = id_ex_curr->ifun;
    ex_mem_next -> icode = id_ex_curr->icode;
    ex_mem_next -> takebranch = e_bcond;
    bool_t my_cond = (id_ex_curr -> icode == I_RRMOVQ && !(ex_mem_next -> takebranch));
    ex_mem_next -> deste = my_cond ? REG_NONE : id_ex_curr -> deste;
    if(!my_cond){
        ex_mem_next -> destm = id_ex_curr -> destm;
        ex_mem_next -> srca = id_ex_curr -> srca;
        ex_mem_next -> status =  id_ex_curr -> status;
    }
}
    
/*************************** Memory stage **************************
 * TODO: update [*mem_wb_next, mem_addr, mem_data, mem_write]
 * you may find these functions useful: 
 * get_word_val()
 * 
 * The pending writeback updates will occur in update_state()
 *******************************************************************/
void do_mem_stage()
{
    /* dummy placeholders, replace them with your implementation */
    mem_wb_next -> valm = 0;
    mem_addr = 0;
    mem_data = 0;
    mem_write = FALSE;
    /* some useful variables for logging purpose */
    bool_t read = FALSE;
    dmem_error = FALSE;
    imem_error = FALSE;

    switch (ex_mem_curr -> icode) {
		case I_HALT:
			status = STAT_HLT;
			break;

		case I_NOP: break;
		
		case I_RRMOVQ: break; // aka CMOVQ

		case I_IRMOVQ: break;
				
		case I_RMMOVQ:
			mem_write = TRUE;
			mem_addr = ex_mem_curr -> vale;
			mem_data = ex_mem_curr -> vala;
			break;
				
		case I_MRMOVQ:
            read = TRUE;
            mem_addr = ex_mem_curr -> vale;
			dmem_error |= !get_word_val(mem, mem_addr, &(mem_wb_next -> valm));
			break;

		case I_ALU: break;

		case I_JMP: break;

		case I_CALL:
            mem_write = TRUE;
            mem_addr = ex_mem_curr -> vale;
            mem_data = ex_mem_curr -> vala;
            break;
            
        case I_RET:
            dmem_error |= !get_word_val(mem, ex_mem_curr -> vala, &(mem_wb_curr -> valm));
            break;

        case I_PUSHQ:
            mem_write = TRUE;
            mem_addr = ex_mem_curr -> vale;
            mem_data = ex_mem_curr -> vala;
            break;
            
        case I_POPQ:
            read = TRUE;
            mem_addr = ex_mem_curr -> vala;
            dmem_error |= !get_word_val(mem, ex_mem_curr -> vala, &(mem_wb_next -> valm));
            break;

        default:
            printf("icode is not valid (%d)", ex_mem_curr -> icode);
            break;
    }

    if (mem_write)
    {
        if (!set_word_val(mem, mem_addr, mem_data))
        {
            sim_log("\tCouldn't write to address 0x%llx\n", mem_addr);
        }
        else
        {
            sim_log("\tWrote 0x%llx to address 0x%llx\n", mem_data, mem_addr);
        }
    }
    /* logging function, do not change this */
    if (read && !dmem_error)
    {
        sim_log("\tMemory: Read 0x%llx from 0x%llx\n",
                mem_wb_next->valm, mem_addr);
    }
    mem_wb_next -> icode = ex_mem_curr -> icode;
    mem_wb_next -> ifun = ex_mem_curr -> ifun;
    mem_wb_next -> vale = ex_mem_curr -> vale;
    mem_wb_next -> destm = ex_mem_curr -> destm;
    mem_wb_next -> deste = ex_mem_curr -> deste;
    mem_wb_next -> status = dmem_error ? STAT_ADR : ex_mem_curr -> status;
}

/******************** Decode & Writeback stage *********************
 * TODO: update [*id_ex_next, wb_destE, wb_valE, wb_destM, wb_valM]
 * you may find these functions useful: 
 * get_reg_val()
 * 
 * you don't perform the operation to really write to memory here
 * the pending writeback updates will occur in update_state()
 *******************************************************************/
void do_wb_stage()
{
    /* dummy placeholders, replace them with your implementation */

    //*****MUST BE REPLACED WITH THE ACTUAL VALUES OF THE DESTINATIONS AND VALUES*********
    wb_destE = mem_wb_curr -> deste;
    wb_valE = mem_wb_curr -> valm;
    wb_destM = mem_wb_curr -> destm;
    wb_valM = mem_wb_curr -> valm;

    if (wb_destE != REG_NONE)
    {
        sim_log("\tWriteback: Wrote 0x%llx to register %s\n",
                wb_valE, reg_name(wb_destE));
        set_reg_val(reg, wb_destE, wb_valE);
    }
    if (wb_destM != REG_NONE)
    {
        sim_log("\tWriteback: Wrote 0x%llx to register %s\n",
                wb_valM, reg_name(wb_destM));
        set_reg_val(reg, wb_destM, wb_valM);
    }
    status = mem_wb_curr -> status == STAT_BUB ? STAT_AOK : mem_wb_curr -> status;
    
}
bool_t pipe_cntl_F_Bubble(){
    return 0;
}
bool_t pipe_cntl_F_Stall(){
    bool_t E_codeIN = id_ex_curr->icode == I_MRMOVQ || id_ex_curr->icode == I_POPQ;
    bool_t dstMIN = id_ex_curr->destm == id_ex_next->srca || 
        id_ex_curr->destm == id_ex_next->srcb;
    bool_t I_RETIN = if_id_curr -> icode == I_RET || id_ex_curr -> icode == I_RET
        || ex_mem_curr -> icode == I_RET; 
    return (E_codeIN && dstMIN) || (I_RETIN);
}

bool_t pipe_cntl_D_Bubble(){
    bool_t E_codeIN = id_ex_curr->icode == I_MRMOVQ || id_ex_curr->icode == I_POPQ;
    bool_t dstMIN = id_ex_curr->destm == id_ex_next->srca || 
        id_ex_curr->destm == id_ex_next->srcb;
     return E_codeIN && dstMIN;
}

bool_t pipe_cntl_D_Stall(){
    bool_t branch = (id_ex_curr->icode == I_JMP) && !(id_ex_curr->icode == ex_mem_next->takebranch);
    bool_t E_codeIN = id_ex_curr->icode == I_MRMOVQ || id_ex_curr->icode == I_POPQ;
    bool_t dstMIN = id_ex_curr->destm == id_ex_next->srca || id_ex_curr->destm == id_ex_next->srcb;
    bool_t I_RETIN = if_id_curr -> icode == I_RET || id_ex_curr -> icode == I_RET
        || ex_mem_curr -> icode == I_RET; 
    return (branch) || !(E_codeIN && dstMIN && I_RETIN);  
}

bool_t pipe_cntl_E_Stall(){
    return 0;
}

bool_t pipe_cntl_E_Bubble(){
    bool_t branch = (id_ex_curr->icode == I_JMP) && !(id_ex_curr->icode == ex_mem_next->takebranch);
    bool_t E_codeIN = id_ex_curr->icode == I_MRMOVQ || id_ex_curr->icode == I_POPQ;
    bool_t dstMIN = id_ex_curr->destm == id_ex_next->srca || id_ex_curr->destm == id_ex_next->srcb;
    return (branch || E_codeIN) && (dstMIN);
}

bool_t pipe_cntl_M_Stall(){
    return 0;
}
bool_t pipe_cntl_M_Bubble(){
    bool_t m_stat = (ex_mem_curr->status == STAT_ADR || ex_mem_curr->status == STAT_INS 
        || ex_mem_curr->status == STAT_HLT);
    bool_t w_stat = (mem_wb_curr->status == STAT_ADR || mem_wb_curr->status == STAT_INS 
        || mem_wb_curr->status == STAT_HLT);
    return m_stat || w_stat; 
}

bool_t pipe_cntl_W_Stall(){
    return (mem_wb_curr->status == STAT_ADR || mem_wb_curr->status == STAT_INS 
                || mem_wb_curr->status == STAT_HLT);
}

bool_t pipe_cntl_W_Bubble(){
    return 0;
}

/* given stall and bubble flag, return the correct control operation */
p_stat_t pipe_cntl(char *name, word_t stall, word_t bubble)
{
    if (stall)
    {
        if (bubble)
        {
            sim_log("%s: Conflicting control signals for pipe register\n",
                    name);
            return P_ERROR;
        }
        else
            return P_STALL;
    }
    else
    {
        return bubble ? P_BUBBLE : P_LOAD;
    }
}


/******************** Pipeline Register Control ********************
 * TODO: implement stalling or insert a bubble for different stages
 * by modifying the control operations of the pipeline registers
 * you may find the util function pipe_cntl() useful
 * 
 * update_pipes() will handle the real control behavior later
 * make sure you have a working PIPE before implementing this
 *******************************************************************/
void do_stall_check()
{
    /* dummy placeholders to show the usage of pipe_cntl() */
    pc_state->op = pipe_cntl("PC", pipe_cntl_F_Stall(), pipe_cntl_F_Bubble());
    if_id_state->op = pipe_cntl("ID", pipe_cntl_D_Stall(), pipe_cntl_D_Bubble());
    id_ex_state->op = pipe_cntl("EX", pipe_cntl_E_Stall(), pipe_cntl_E_Bubble());
    ex_mem_state->op = pipe_cntl("MEM", pipe_cntl_M_Stall(), pipe_cntl_M_Bubble());
    mem_wb_state->op = pipe_cntl("WB", pipe_cntl_W_Stall(), pipe_cntl_W_Bubble());
    /*
    seperate method for fetch decode  stat = done
    "" "" "" decode execute stat 
    "" "" "" execute memory
    "" "" "" memory write back
    */
}

/*
  Run pipeline until one of following occurs:
  - An error status is encountered in WB.
  - max_instr instructions have completed through WB
  - max_cycle cycles have been simulated

  Return number of instructions executed.
  if statusp nonnull, then will be set to status of final instruction
  if ccp nonnull, then will be set to condition codes of final instruction
*/
word_t sim_run_pipe(word_t max_instr, word_t max_cycle, byte_t *statusp, cc_t *ccp)
{
    word_t icount = 0;
    word_t ccount = 0;
    byte_t run_status = STAT_AOK;
    while (icount < max_instr && ccount < max_cycle)
    {
        run_status = sim_step_pipe(max_instr - icount, ccount);
        if (run_status != STAT_BUB)
            icount++;
        if (run_status != STAT_AOK && run_status != STAT_BUB)
            break;
        ccount++;
    }
    if (statusp)
        *statusp = run_status;
    if (ccp)
        *ccp = cc;
    return icount;
}

/* If dumpfile set nonNULL, lots of status info printed out */
void sim_set_dumpfile(FILE *df)
{
    dumpfile = df;
}

/*
 * sim_log dumps a formatted string to the dumpfile, if it exists
 * accepts variable argument list
 */
void sim_log(const char *format, ...)
{
    if (dumpfile)
    {
        va_list arg;
        va_start(arg, format);
        vfprintf(dumpfile, format, arg);
        va_end(arg);
    }
}

/**************************************************************
 * Part 4: Code for implementing pipelined processor simulators
 * Do not change any of these
 *************************************************************/

/******************************************************************************
 *	defines
 ******************************************************************************/

#define MAX_STAGE 10

/******************************************************************************
 *	static variables
 ******************************************************************************/

static pipe_ptr pipes[MAX_STAGE];
static int pipe_count = 0;

/******************************************************************************
 *	function definitions
 ******************************************************************************/

/* Create new pipe with count bytes of state */
/* bubble_val indicates state corresponding to pipeline bubble */
pipe_ptr new_pipe(int count, void *bubble_val)
{
    pipe_ptr result = (pipe_ptr)malloc(sizeof(pipe_ele));
    result->current = malloc(count);
    result->next = malloc(count);
    memcpy(result->current, bubble_val, count);
    memcpy(result->next, bubble_val, count);
    result->count = count;
    result->op = P_LOAD;
    result->bubble_val = bubble_val;
    pipes[pipe_count++] = result;
    return result;
}

/* Update all pipes */
void update_pipes()
{
    int s;
    for (s = 0; s < pipe_count; s++)
    {
        pipe_ptr p = pipes[s];
        switch (p->op)
        {
        case P_BUBBLE:
            /* insert a bubble into the next stage */
            memcpy(p->current, p->bubble_val, p->count);
            break;

        case P_LOAD:
            /* copy calculated state from previous stage */
            memcpy(p->current, p->next, p->count);
            break;
        case P_ERROR:
            /* Like a bubble, but insert error condition */
            memcpy(p->current, p->bubble_val, p->count);
            break;
        case P_STALL:
        default:
            /* do nothing: next stage gets same instr again */
            ;
        }
        if (p->op != P_ERROR)
            p->op = P_LOAD;
    }
}

/* Set all pipes to bubble values */
void clear_pipes()
{
    int s;
    for (s = 0; s < pipe_count; s++)
    {
        pipe_ptr p = pipes[s];
        memcpy(p->current, p->bubble_val, p->count);
        memcpy(p->next, p->bubble_val, p->count);
        p->op = P_LOAD;
    }
}

/*************** Bubbled version of stages *************/

pc_ele bubble_pc = {0, STAT_AOK};
if_id_ele bubble_if_id = {I_NOP, 0, REG_NONE, REG_NONE,
                          0, 0, STAT_BUB, 0};
id_ex_ele bubble_id_ex = {I_NOP, 0, 0, 0, 0,
                          REG_NONE, REG_NONE, REG_NONE, REG_NONE,
                          STAT_BUB, 0};

ex_mem_ele bubble_ex_mem = {I_NOP, 0, FALSE, 0, 0,
                            REG_NONE, REG_NONE, STAT_BUB, 0};

mem_wb_ele bubble_mem_wb = {I_NOP, 0, 0, 0, REG_NONE, REG_NONE,
                            STAT_BUB, 0};
