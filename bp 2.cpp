/* 046267 Computer Architecture - HW #1                                 */
/* This file holds the implementation of the predictor simulator */

#include "bp_api.h"
#include <vector> 
#include <cmath> 
#include <iostream>

int update_hist (int history,bool taken,int historySize);
int Share_addr (int history, uint32_t pc , int share, int historySize);
uint32_t calc_tag (uint32_t pc, int tagSize,int num_of_lines);
void update_fsm (int* fsm_table ,bool taken,int index);

class Branch_pred; 
class BTB_line; 

enum fsm_state {SNT = 0, WNT = 1, WT = 2, ST = 3}; 
Branch_pred* ptr_BP = nullptr; 

class BTB_line {
    public:
        uint32_t tag;
        bool isGlobalHist;
        bool isGlobalTable;
        int history;
        unsigned historySize;
        fsm_state fsmState; 
        int* fsm_table;
        uint32_t targetPc;

        BTB_line(uint32_t tag, bool isGlobalHist, 
            bool isGlobalTable, unsigned historySize, fsm_state fsmState,
            uint32_t targetPc) : tag(tag),
            isGlobalHist(isGlobalHist), isGlobalTable(isGlobalTable),
            historySize(historySize), fsmState(fsmState)
            {
                history = 0; 
                /*Local FSM table*/
                if(isGlobalTable == false)
                {
                    int size = pow(2, historySize); 
                    fsm_table=new int[size];
                    //iniilizing each line in fsm table to the given state in input
                    for(int i = 0; i < size; i++)
                    {
                        fsm_table[i] = fsmState;
                    }
                }
                
            }
        virtual ~BTB_line(){}
};

/*Branch Predictor class*/
class Branch_pred {
    public:
        unsigned btbSize;
        unsigned historySize;
        unsigned tagSize;
        fsm_state fsmState;
        bool isGlobalHist;
        bool isGlobalTable;
        int Shared;
        bool* valid_bit;
        std::vector<BTB_line> BP_table;
        int history;  
        int* fsm_table;
        unsigned flush_num;           // Machine flushes
        unsigned br_num;      	      // Number of branch instructions
        
        /*Brunch_pred Constructor*/
        Branch_pred(unsigned btbSize, unsigned historySize, unsigned tagSize, 
            fsm_state fsmState, bool isGlobalHist, bool isGlobalTable,
            int Shared): btbSize(btbSize), historySize(historySize),
            tagSize(tagSize), fsmState(fsmState), isGlobalHist(isGlobalHist),
            isGlobalTable(isGlobalTable), Shared(Shared)
            {
                flush_num = 0; 
                br_num = 0;
                history= 0;
                valid_bit = new bool[btbSize];
                for( int i = 0; i < (int)btbSize; i++)
                {
                    BTB_line* ptr_BTB_line = new BTB_line(-1, false, false, 
                        historySize, fsmState, 0); 
                    BP_table.push_back(*ptr_BTB_line); //adding new line to BTB table
                    valid_bit[i]=false; 
                }
                //creating global fsm table 
                if(isGlobalTable)
                {
                    int size = pow(2, historySize); 
                    fsm_table=new int[size];
                    for(int i = 0; i < size; i++)
                    {
                        //initilizing each line in fsm table to the given state in input
                        fsm_table[i] = fsmState;
                    }
                } 
            }

        virtual ~Branch_pred(){} /*Branch_pred destructor*/
};



int BP_init(unsigned btbSize, unsigned historySize, unsigned tagSize, 
    unsigned fsmState, bool isGlobalHist, bool isGlobalTable, int Shared)
{
    ptr_BP = new Branch_pred(btbSize, historySize, tagSize, (fsm_state)fsmState, 
        isGlobalHist, isGlobalTable, Shared);
    if(ptr_BP == nullptr)
    {
        return -1; 
    }
	return 0;
}

bool BP_predict(uint32_t pc, uint32_t *dst)
{
    uint32_t mask = 0; 
    int BP_index = 0; 
    int num_of_lines=log2(ptr_BP->btbSize); 
    for( int i = 0 ; i < num_of_lines; i++ )
    {
        mask = mask << 1; 
        mask++; 
    }
    BP_index = (pc >> 2) & (mask); 
    uint32_t tag = calc_tag( pc, ptr_BP->tagSize, ptr_BP ->btbSize); 
    if((ptr_BP->BP_table[BP_index].tag ==tag) && ptr_BP->valid_bit[BP_index])
    {
        if(!ptr_BP->isGlobalHist && !ptr_BP->isGlobalTable ) //Local history & Local fsm table
        {
            if( ptr_BP->BP_table[BP_index].fsm_table
                [ptr_BP->BP_table[BP_index].history] <= 1) //check not taken
            {
			    *dst = pc + 4;
			    return false;
		    }
            else 
            {
                *dst = ptr_BP->BP_table[BP_index].targetPc;
                return true; 
            }

        }
        else if(ptr_BP->isGlobalHist && !ptr_BP->isGlobalTable) ////Global history & Local fsm table
        {
            if( ptr_BP->BP_table[BP_index].fsm_table[ptr_BP->history] <= 1) //check not taken
			{
                *dst = pc+4;
                return false;
            }
            else 
            {
                *dst= ptr_BP->BP_table[BP_index].targetPc;
			    return true;
            }
		}
        else if(!ptr_BP->isGlobalHist && ptr_BP->isGlobalTable) //Local history & Global fsm table
        {
            if(ptr_BP->fsm_table[Share_addr(ptr_BP->BP_table[BP_index].history,
                pc, ptr_BP->Shared, ptr_BP->historySize)] <= 1)
            
            {
			    *dst = pc+4;
		         return false;
		    }
		    else{
			    *dst = ptr_BP->BP_table[BP_index].targetPc;
			    return true;
		    } 
		}
        else //Global history & Global fsm table
        {
            if(ptr_BP->fsm_table[Share_addr(ptr_BP->BP_table[BP_index].history,
                pc, ptr_BP->Shared,ptr_BP->BP_table[BP_index].historySize)]<= 1)
            {
                *dst = pc+4;
                return false;
		    }
		    else{
                *dst= ptr_BP->BP_table[BP_index].targetPc;
                return true;
		    }
        }
    }
    else if( (ptr_BP->BP_table[BP_index].tag != tag) && 
        ptr_BP->valid_bit[BP_index] )
    {
		ptr_BP->valid_bit[BP_index] = false;
		ptr_BP->BP_table[BP_index].history = 0;
		int size = pow(2, ptr_BP->BP_table[BP_index].historySize);
		for(int i=0 ; i < size ; i++)
			ptr_BP->BP_table[BP_index].fsm_table[i]= ptr_BP->fsmState;
		    ptr_BP->BP_table[BP_index].tag = tag;
  	}
    *dst = pc+4;
	return false;
}

void BP_update(uint32_t pc, uint32_t targetPc, bool taken, uint32_t pred_dst)
{
    ptr_BP->br_num++; //update branch num 
    uint32_t mask = 0;
    uint32_t dst = 0; 
	int BP_index = 0;
    int num_of_lines = log2(ptr_BP->btbSize); 

    uint32_t tag = calc_tag(pc ,ptr_BP->tagSize ,ptr_BP ->btbSize);
    bool taken_prediction = BP_predict(pc, &dst);

    if( taken_prediction != taken ) /*wrong taken prediction*/
    {
        ptr_BP->flush_num++;
    }
    else /*right taken prediction*/
    { 
        if( ( (pred_dst!= pc+4 ) && (!taken) )|| 
            ( (pred_dst != targetPc) && (taken) ) ) 
        {
            ptr_BP->flush_num++;
        }
    }
	for (int i = 0; i < num_of_lines; i++) {
	    mask = mask << 1;
	    mask++;
	}
	BP_index = pc>>2 & (mask);

	ptr_BP->BP_table[BP_index].targetPc = targetPc;

	if(ptr_BP->valid_bit[BP_index] == false)
    {
        ptr_BP->valid_bit[BP_index] = true;
        ptr_BP->BP_table[BP_index].tag = tag;
	}
    

    if ( ptr_BP->isGlobalHist && ptr_BP->isGlobalTable )
    {
        update_fsm(ptr_BP->fsm_table, taken, Share_addr(ptr_BP->history,pc,
            ptr_BP->Shared, ptr_BP->historySize));
        ptr_BP->history= update_hist(ptr_BP->history,taken,ptr_BP->historySize);
        
    }
    else  if (ptr_BP->isGlobalHist && !ptr_BP->isGlobalTable)
    {  
        update_fsm(ptr_BP->BP_table[BP_index].fsm_table,taken, ptr_BP->history);
        ptr_BP->history= update_hist(ptr_BP->history,taken,ptr_BP->historySize);
    }

    else if (!ptr_BP->isGlobalHist && ptr_BP->isGlobalTable)
    {
        update_fsm(ptr_BP->fsm_table,taken, Share_addr(
            ptr_BP->BP_table[BP_index].history,pc,ptr_BP->Shared,
            ptr_BP->historySize));
        ptr_BP->BP_table[BP_index].history = update_hist(
            ptr_BP->BP_table[BP_index].history,taken,ptr_BP->historySize);
    }

    else 
    {   

        // A branch command already exists in this index - override tag, and reset history and fsm_table
        if(ptr_BP->valid_bit[BP_index] == true){  
            ptr_BP->BP_table[BP_index].tag = tag;
            ptr_BP->BP_table[BP_index].history = 0;
            int size = pow(2, ptr_BP->BP_table[BP_index].historySize); 
            for(int i = 0; i < size; i++)
                {
                    ptr_BP->BP_table[BP_index].fsm_table[i] = ptr_BP->BP_table[BP_index].fsmState;
                }
             return;

        }
        update_fsm(ptr_BP->BP_table[BP_index].fsm_table,taken, 
            ptr_BP->BP_table[BP_index].history); 
        ptr_BP->BP_table[BP_index].history = update_hist(
            ptr_BP->BP_table[BP_index].history,taken,ptr_BP->historySize);
    }
	return;
}

void BP_GetStats(SIM_stats *curStats)
{
    curStats->br_num = ptr_BP->br_num;
    curStats->flush_num = ptr_BP->flush_num;
    /*30 bits fo pc address, 1 for valid bit*/
    if( ptr_BP->isGlobalHist && ptr_BP->isGlobalTable)
    {
        curStats->size = ptr_BP->historySize + (ptr_BP->btbSize)*
            (ptr_BP-> tagSize + 30 + 1) + 2*pow(2,ptr_BP->historySize); 
        delete[] ptr_BP->fsm_table;
    }
	
    else if ( !ptr_BP->isGlobalHist && ptr_BP->isGlobalTable )
    {
        curStats->size = (ptr_BP->btbSize)*(ptr_BP->tagSize +30 + 1 + 
            ptr_BP->historySize) + 2*pow(2,ptr_BP->historySize);
        delete[] ptr_BP->fsm_table;
    }
    else if (  ptr_BP->isGlobalHist && !ptr_BP->isGlobalTable )
    {
        curStats->size =  ptr_BP->historySize + (ptr_BP->btbSize) *
            (ptr_BP->tagSize + 30 + 1 + 2*pow(2,ptr_BP->historySize));
    }
    else
    {
  	    curStats->size = (ptr_BP->btbSize) * (ptr_BP->tagSize +30 + 1 +
            2*pow(2,ptr_BP->historySize) + ptr_BP->historySize);
    }
    delete[] ptr_BP->valid_bit;
    ptr_BP->BP_table.clear();
    if (ptr_BP != nullptr)
    {
        delete ptr_BP; 
    }
	return;
}

void update_fsm (int* fsm_table ,bool taken,int index)
{
    if (taken)
    {
        if (fsm_table[index] < 3)
        {
            fsm_table[index]++;
        }
    }
    else
    {
        if (fsm_table[index] > 0)
        {
            fsm_table[index]--;
        }

    }
}

uint32_t calc_tag (uint32_t pc, int tagSize,int num_of_lines)
{
    uint32_t mask = 0;
    for (int i = 0; i < tagSize; i++)
    {
        mask = mask << 1;
        mask++;
    }
    /*tag begins from bit 2+log2(BTBsize)*/
    return (pc >> (2 + num_of_lines) & (mask)); 
}

int Share_addr (int history, uint32_t pc , int share, int historySize)
{

    uint32_t mask = pow(2,historySize) - 1;
    int shared_address;
    if (share == 1) /*LSB share*/
    {
        shared_address = history ^ ((pc>>2) & mask);
        return shared_address;
    }

    else if (share==2) /*MSB share*/
    {
        shared_address = history ^ ((pc>>16) & mask);
        return shared_address;
    }
    /*no share used*/
    return history;
}

int update_hist (int history,bool taken,int historySize)
{
    uint32_t mask=0;
    for (int i=0; i < historySize; i++)
    {
        mask = mask << 1;
        mask++;
    }
    history = history << 1;
    if(taken)
    {
        history++;
    }
    return (history & mask);
}

