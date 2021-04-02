/***********************************************************************************
Created by Mohsen Safari.
************************************************************************************/
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <math.h>
#include <cuda.h>

///////////////////////////////////////////////////////////////////////////////Operations
/*@
requires 0 <= n;
requires n < |xs|;
pure int get(seq<int> xs, int n) = xs[n];
@*/

/*@
requires 0 <= p;
ensures n == 2 ==> p < \result;
pure int exp(int n, int p) = 0 < p ? n * exp(n, p - 1) : 1;
@*/

/*@
requires n <= |xs|;
ensures n < 0 ==> |Take(xs, n)| == 0;
ensures 0 <= n ==> |Take(xs, n)| == n;
ensures (\forall int i; 0 <= i && i < n; xs[i] == get(Take(xs, n), i));
pure seq<int> Take(seq<int> xs, int n) =
	0 < n ? seq<int> { head(xs) } + Take(tail(xs), n - 1) : seq<int> { };
@*/

/*@
ensures |xs| == 0 ==> \result == 0;
ensures |xs| == 1 ==> \result == head(xs);
pure int intsum(seq<int> xs) =
	0 < |xs| ? head(xs) + intsum(tail(xs)) : 0;
@*/

/*@
requires 0 <= i && i <= |xs|;
ensures |\result| == |xs| - i;
ensures (\forall int j; 0 <= j && j < |\result|; \result[j] == intsum(Take(xs, i+j+1))); 
pure seq<int> psum(seq<int> xs, int i) =
	i < |xs| ? seq<int> { intsum(Take(xs, i + 1)) } + psum(xs, i + 1) : seq<int> { };
@*/

// TODO use this version instead of the above `psum` (the above version is just a helper definition).
/*@
ensures |\result| == |xs|;
ensures (\forall int j; 0 <= j && j < |\result|; \result[j] == intsum(Take(xs, j+1))); 
pure seq<int> psum2(seq<int> xs) = psum(xs, 0);
@*/

/*@
requires |input| >= 0;
requires i >= 0;
requires i <= |input|;
requires offset > 0;
requires offset <= |input|*2;
ensures |\result| == |input| - i;
ensures (\forall int j; 0 <= j && j < |\result|; \result[j] == intsum(Take(input, i + j + 1)) - intsum(Take(input, i + j + 1 - offset)));
pure seq<int> partial_prefixsum(seq<int> input, int i, int offset) = 	
i < |input| ? seq<int> {intsum(Take(input, i + 1)) - intsum(Take(input, i + 1 - offset))} + partial_prefixsum(input, i + 1, offset)	: seq<int> { };	
@*/

/////////////////////////////////////////////////////////////////////////////////////////////////Lemmas
/*@
requires |xs| <= 1;
requires i >= 0;
requires offset > 0;
requires offset <= |xs|;
ensures \result && (i < |xs| ==> xs == partial_prefixsum(xs, i, offset*2));
pure bool lemma_partial_prefixsum_base(seq<int> xs, int i, int offset) = true;
@*/	

/*@
requires 0 < n;
ensures \result && exp(2, n) == 2 * exp(2, n - 1);
pure bool lemma_exp2_red_mult(int n) = true;
@*/	

/*@
requires 0 < n;
ensures \result && exp(2, n) / 2 == exp(2, n - 1);
pure bool lemma_exp2_red_div(int n) = true;
@*/

/*@
requires 0 <= n;
ensures \result && 0 < exp(2, n);
pure bool lemma_exp2_positive(int n) =
  0 < n ? lemma_exp2_positive(n - 1) : true;
@*/

/*@
requires 0 <= i;
requires i <= j;
ensures \result && exp(2, i) <= exp(2, j);
pure bool lemma_exp2_leq(int i, int j) =
	0 < i ? lemma_exp2_leq(i - 1, j - 1) : lemma_exp2_positive(j);
@*/

/*@
requires 0 <= i && i < |xs|;
ensures \result && get(psum2(xs), i) == intsum(Take(xs, i+1));
pure bool lemma_psum_get(seq<int> xs, int i) =
  0 < |xs| ? (0 < i ? lemma_psum_get(tail(xs), i - 1) : true)
           : true;
@*/

/*@
requires j >= 0 && j <= |xs|;
ensures \result && (\forall int i; j <= i && i < |xs|; get(psum2(xs), i) == intsum(Take(xs, i+1)));
pure bool lemma_psum_get_all(seq<int> xs, int j) =
  j < |xs| ? lemma_psum_get(xs, j) && lemma_psum_get_all(xs, j+1) : true;
@*/

/*@
requires |xs| >= 0;
requires |ys| >= 0;
ensures \result && |xs| == 0 ==> intsum(xs + ys) == intsum(ys);
ensures \result && |ys| == 0 ==> intsum(xs + ys) == intsum(xs);
ensures \result && |xs + ys| == |xs| + |ys|;
ensures \result && intsum(tail(xs) + ys) == intsum(tail(xs)) + intsum(ys);
ensures \result && intsum(xs + ys) == intsum(xs) + intsum(ys);
pure bool lemma_intsum_app(seq<int> xs, seq<int> ys) =
  0 < |xs| ? lemma_intsum_app(tail(xs), ys) && tail(xs) + ys == tail(xs + ys) : true;
@*/

/*@
ensures \result && intsum(seq<int> { }) == 0;
pure bool lemma_intsum_zero() = true;
@*/

/*@
ensures \result && intsum(seq<int> { x }) == x;
pure bool lemma_intsum_single(int x) =
  tail(seq<int> { x }) == seq<int> { } && lemma_intsum_zero();
@*/

/*@
requires 0 <= n && n < |xs|;
ensures \result && Take(xs, n + 1) == Take(xs, n) + seq<int> { xs[n] };
pure bool missing_lemma_2(seq<int> xs, int n) =
  1 <= n ? missing_lemma_2(tail(xs), n - 1) : true;
@*/

/*@
requires |xs| >= 0;
requires i >= 0;
requires i < |xs|;
//ensures \result && (xs[i] == intsum(Take(xs, i + 1)) - intsum(Take(xs, i)));
pure bool lemma_intsum_Take(seq<int> xs, int i) =
	missing_lemma_2(xs, i) &&
	Take(xs, i + 1) == Take(xs, i) + seq<int> {xs[i]} &&
	lemma_intsum_app(Take(xs, i), seq<int> {xs[i]}) &&
	intsum( Take(xs, i) + seq<int> {xs[i]} ) == intsum(Take(xs, i)) + intsum(seq<int> {xs[i]}) &&
	intsum(Take(xs, i + 1)) == intsum(Take(xs, i)) + intsum(seq<int> {xs[i]}) &&
	lemma_intsum_single(xs[i]) &&
	xs[i] == intsum(seq<int> {xs[i]}) &&
  intsum(Take(xs, i + 1)) - intsum(Take(xs, i)) == intsum(Take(xs, i)) + intsum(seq<int> {xs[i]}) - intsum(Take(xs, i)) &&
  intsum(Take(xs, i + 1)) - intsum(Take(xs, i)) == intsum(seq<int> {xs[i]}) &&
  xs[i] == intsum(Take(xs, i + 1)) - intsum(Take(xs, i)) &&
  true;
@*/

////////////////////////////////////////////////////////////////////////////////
//Kernel
////////////////////////////////////////////////////////////////////////////////
/*@ 
//given seq<int> input_seq;
context_everywhere output != NULL;
context_everywhere k == 10;
//context_everywhere |input_seq| == exp(2, k);
context_everywhere opencl_gsize == exp(2, k);
context_everywhere opencl_gcount == 1;
//requires \pointer_index(output, \ltid, 1\2); 
//requires \ltid >= 1 ==> \pointer_index(output, \ltid - 1, 1\2); 
ensures \pointer_index(output, \ltid, 1\2);
@*/
__global__ void CUDA_Kernel_Kogge_Stone(int* output, int k)
{
  int tid = threadIdx.x;
  //@ assert tid == \ltid;
  
  //@ inhale \pointer_index(output, tid, 1\2); 
  //@ inhale tid >= 1 ==> \pointer_index(output, tid - 1, 1\2); 
  
  //@ ghost seq<int> out; 
  //@ assume |out| == exp(2, k);
  //@ assume output[tid] == out[tid];
  
  int offset = 1;
	int temp;
  //@ ghost seq<int> temp_seq = out; 
  //lemma_intsum_Take(temp_seq, tid);
	//@ assert missing_lemma_2(temp_seq, tid);
	//@ assert Take(temp_seq, tid + 1) == Take(temp_seq, tid) + seq<int> {temp_seq[tid]};
	//@ assert lemma_intsum_app(Take(temp_seq, tid), seq<int> {temp_seq[tid]});
	//@ assert intsum( Take(temp_seq, tid) + seq<int> {temp_seq[tid]} ) == intsum(Take(temp_seq, tid)) + intsum(seq<int> {temp_seq[tid]});
	//@ assert intsum(Take(temp_seq, tid + 1)) == intsum(Take(temp_seq, tid)) + intsum(seq<int> {temp_seq[tid]});
	//@ assert lemma_intsum_single(temp_seq[tid]);
	//@ assert temp_seq[tid] == intsum(seq<int> {temp_seq[tid]});
  
  //@ assert tid < offset ==> output[tid] == temp_seq[tid];
  
  //@ assert temp_seq[tid] == intsum(Take(temp_seq, tid + 1)) - intsum(Take(temp_seq, tid));

 
    
  /*@
	loop_invariant offset >= 1;
	loop_invariant |temp_seq| == |out|;
	loop_invariant offset < 2 * exp(2, k);
	loop_invariant \pointer_index(output, tid, 1\2); 
	loop_invariant tid >= offset ==> \pointer_index(output, tid - offset, 1\2); 
	loop_invariant temp_seq[tid] == intsum(Take(out, tid + 1)) - intsum(Take(out, tid + 1 - offset));
	loop_invariant tid < offset ==> temp_seq[tid] == intsum(Take(out, tid + 1));
	loop_invariant tid < offset ==> temp_seq[tid] == get(psum2(out), tid);
	loop_invariant temp_seq[tid] == get(partial_prefixsum(out, 0, offset), tid);
	loop_invariant tid < offset ==> output[tid] == temp_seq[tid]; 
  @*/
	while(offset < exp(2, k))
	{
		
		temp = output[tid];
		
		if (tid >= offset)
		{ 
			temp = temp + output[tid - offset];	
		}
		//@ assert tid < offset ==> temp == output[tid];
		//@ assert tid >= offset ==> temp == output[tid] + output[tid - offset];
		
     
    
    /*@
      context_everywhere |temp_seq| == exp(2, k);
			context tid >= 0 && tid < exp(2, k);
			context offset >= 1 && offset < exp(2, k);
			requires \pointer_index(output, tid, 1\2);
			requires tid >= offset ==> \pointer_index(output, tid - offset, 1\2);
			requires tid >= offset ==> temp == output[tid] + output[tid - offset];
      requires tid < offset  ==> output[tid] == temp_seq[tid];				
			ensures \pointer_index(output, tid, 1);	
      ensures tid < offset  ==> output[tid] == temp_seq[tid];	
    @*/
    __syncthreads();
    
   
		
		if (tid >= offset)
		{ 
			output[tid] = temp;
		}

    
		//@ assert tid < offset  ==> output[tid] == temp_seq[tid];
		//@ ghost temp_seq = partial_prefixsum(out, 0, offset * 2);
		//@ assert temp_seq[tid] == intsum(Take(out, tid + 1)) - intsum(Take(out, tid + 1 - offset * 2));
		//@ assert tid < offset * 2 ==> temp_seq[tid] == intsum(Take(out, tid + 1));
		//@ assert tid < offset * 2 ==> temp_seq[tid] == get(psum2(out), tid);
		//@ assert temp_seq[tid] == get(partial_prefixsum(out, 0, offset * 2), tid);
		
		
    
    
    /*@
      context_everywhere |temp_seq| == exp(2, k);
			context tid >= 0 && tid < exp(2, k);
			context offset >= 1 && offset < exp(2, k);
			requires \pointer_index(output, \ltid, 1);
      requires tid < offset ==> output[\ltid] == temp_seq[tid];
			ensures \pointer_index(output, tid, 1\2);
			ensures tid >= offset * 2 ==> \pointer_index(output, tid - offset * 2, 1\2);
      ensures tid < offset * 2 ==> output[tid] == temp_seq[tid]; 
    @*/
    __syncthreads(); 
    
		offset = offset * 2;
		
		
  }
	
	//@ assert temp_seq[tid] == get(psum2(out), tid);
	//@ assert output[tid] == temp_seq[tid];
	//@ assert output[tid] == get(psum2(out), tid);
	// assert input[tid] == out[tid];
  
  
  
}

////////////////////////////////////////////////////////////////////////////////
// CUDA Functions
////////////////////////////////////////////////////////////////////////////////
//@ ensures \pointer(\result, N, write);
int *vercorsMallocInt(int N);
void vercorsFreeInt(int *ar);
//@ ensures \pointer(\result, N, write);
int *vercorsCudaMallocInt(int N);
void vercorsCudaFreeInt(int *addr);
//@ context \pointer(src, N, read) ** \pointer(tgt, N, write);
//@ ensures (\forall int i; i >= 0 && i < N; src[i] == tgt[i]);
void vercorsCudaMemcpyInt(int *tgt, int *src, int N, int direction); 

////////////////////////////////////////////////////////////////////////////////
// Main Program
////////////////////////////////////////////////////////////////////////////////
int CUDA_Host_Kogge_Stone( int argc, char** argv)
{
  int k = 10; // size of the input is 2^k
  
  int* host_input = vercorsMallocInt(exp(2, k)); // size of the host_input is 2^k
  int* host_output = vercorsMallocInt(exp(2, k)); // size of the host_output is 2^k
  
  //@ loop_invariant k == 10;
  //@ loop_invariant q >= 0 && q <= exp(2, k);
  //@ loop_invariant \pointer(host_input, exp(2, k), write) ** \pointer(host_output, exp(2, k), write);
  //@ loop_invariant (\forall int i; i >= 0 && i < q; host_input[i] == host_output[i]);
  for(int q=0; q<exp(2, k); q++)
  {
    host_output[q] = host_input[q];
  }
  
  //Copy the arrays to device memory
  int* device_output;
  device_output = vercorsCudaMallocInt(exp(2, k));
  //@ assert \pointer(device_output, exp(2, k), write);
  vercorsCudaMemcpyInt(device_output, host_output, exp(2, k), cudaMemcpyHostToDevice) ;
  //@ assert (\forall int i; i >= 0 && i < exp(2, k); host_output[i] == device_output[i]);
  //@ assert (\forall int i; i >= 0 && i < exp(2, k); host_output[i] == host_input[i]);
  //@ assert (\forall int i; i >= 0 && i < exp(2, k); device_output[i] == host_input[i]);
  
  //setup execution parameters
	int num_of_blocks = 1;
	int num_of_threads_per_block = exp(2, k);

  
  //Kernel launch
  CUDA_Kernel_Kogge_Stone<<< /*grid*/num_of_blocks, /*threads*/num_of_threads_per_block/*, 0*/ >>>(device_output, k);
  //@ assert \pointer(device_output, exp(2, k), 1\2);
  //@ assert \pointer(host_input, exp(2, k), write);
  // copy result from device to host
  //vercorsCudaMemcpyInt(host_output, device_output, exp(2, k), cudaMemcpyDeviceToHost);
  
  // cleanup memory
  vercorsFreeInt(host_output);
  vercorsCudaFreeInt(device_output);
  
}
