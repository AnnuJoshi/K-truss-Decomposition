/* -*- mode: C -*-  */
/* 
   IGraph library.
   Copyright (C) 2006-2012  Gabor Csardi <csardi.gabor@gmail.com>
   334 Harvard street, Cambridge, MA 02139 USA
   
   This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 2 of the License, or
   (at your option) any later version.
   
   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.
   
   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 
   02110-1301 USA

*/
#include "igraph_layout.h"
#include "igraph_random.h"
#include "igraph_components.h"
#include "igraph_types_internal.h"

#include "igraph_adjlist.h"
#include "igraph_community.h"
#include "igraph_memory.h"
#include "igraph_interface.h"
#include "igraph_iterators.h"
#include "config.h"

#include "igraph_datatype.h"
#include "igraph_attributes.h"
#include "igraph_memory.h"

#include "igraph_error.h"
#include "igraph_random.h"
#include "igraph_qsort.h"

#include "igraph_interrupt_internal.h"

#include "igraph_structural.h"
#include "igraph_constructors.h"
#include "igraph_conversion.h"

#include "igraph_attributes.h"

#include <assert.h>
#include <stdlib.h>
#include <stdarg.h>		/* va_start & co */
#include <math.h>
#include <string.h>   /* memset */
#include <stdio.h>
#include <time.h>
/**
 * \function igraph_trussness 
 * \brief Finding the trussness of the edges in a network.
 *
 * The k-truss of a graph is a maximal subgraph in which each edge
 * participates in at least k-2 triangles in the subgraph. 
 * The trussness of an edge is the highest order 
 * of a k-truss containing the edge.
 * 
 * </para><para>
 * This function implements the algorithm presented in Jia Wang
 * , James Cheng "Truss decomposition in massive networks.": An O(m^1.5) Algorithm for Truss
 * Decomposition of Networks. 
 * \param graph The input graph.
 * \param truss Pointer to an initialized vector, the result of the
 *        computation will be stored here. It will be resized as
 *        needed. For each edge it contains the highest order of a
 *        truss containing the edge.
 * \return Error code.
 *
 * Time complexity: O(|E|^1.5), the number of edges.
 */

int binsort(igraph_matrix_t *arr,igraph_vector_t * edges,igraph_vector_t* sindex,long int h,long int max)
 {
 long int tmpsize,i,j,ind=0;
 igraph_vector_ptr_t bin;
 igraph_vector_ptr_init(&bin,max+1);
 igraph_vector_t* tmp;
 igraph_real_t ed;
 for(i=0;i<=max;i++)
   {
   igraph_vector_t* temp=igraph_Calloc(1,igraph_vector_t);
   VECTOR(bin)[i]=temp;
   } 

 
 for(i=0;i<=h;i++)
   {
   tmp=VECTOR(bin)[(long int)MATRIX(*arr,i,1)];
   igraph_vector_push_back(tmp,MATRIX(*arr,i,0));
   }

 for(i=0;i<=max;i++)
   {
   
   tmp=VECTOR(bin)[i];
   tmpsize=igraph_vector_size(tmp);
   if(tmpsize>0)
   VECTOR(*sindex)[i]=ind;
   else
   VECTOR(*sindex)[i]=-1;
   for(j=0;j<tmpsize;j++)
     {
      ed=VECTOR(*tmp)[j];
     MATRIX(*arr,ind,0)=ed;
     MATRIX(*arr,ind,1)=i;
     VECTOR(*edges)[(long int)ed]=ind;
     ind++;
     }
   }

 return 0;
 }

int igraph_trussness(const igraph_t *graph, igraph_vector_t *truss) {

 long int no_of_edges=igraph_ecount(graph);
 igraph_integer_t u,v,eid1,eid2,temp,nsize;
 igraph_vector_int_t *neis1,*neis2,result,*w;
 igraph_matrix_t edge_sup;
 igraph_bool_t* deleted;
 igraph_vector_t edges,sindex;
 long int max=0,d1,d2,i,j,z,ind1,ind2,p,sup1,sup2,tmp,eid=0,k=2,counter=1,ind=0,vsindex;
 igraph_adjlist_t al; 
 igraph_matrix_init(&edge_sup, no_of_edges,2);
 igraph_vector_init(truss,no_of_edges);
 igraph_vector_init(&edges,no_of_edges);
 
 //deleted array is to mark edges deleted.
 deleted=igraph_Calloc(no_of_edges,int);
 if (deleted==0) {
    IGRAPH_ERROR("Cannot calculate k-truss", IGRAPH_ENOMEM);
    }
 IGRAPH_FINALLY(igraph_free,deleted);

 igraph_adjlist_init(graph,&al,IGRAPH_ALL);
 
 //compute support of each edge.
 for(i=0;i<no_of_edges;i++)
    {
    igraph_vector_int_init(&result,0);
   
    v=IGRAPH_FROM(graph,i);
    u=IGRAPH_TO(graph,i);
   
    neis1=igraph_adjlist_get(&al,v);
    neis2=igraph_adjlist_get(&al,u);
    igraph_vector_int_intersect_sorted(neis1,neis2,&result);
    
    VECTOR(edges)[i]=i;
    MATRIX(edge_sup,i,0)=i;  
    MATRIX(edge_sup,i,1)=igraph_vector_int_size(&result);
    if(max<MATRIX(edge_sup,i,1))
       max=MATRIX(edge_sup,i,1);
    } 
 
 igraph_vector_init(&sindex,max+1);
 //sort the edge_sup based on support of edges. 
 binsort(&edge_sup,&edges,&sindex,no_of_edges-1,max);

 //counter denotes count of deleted edges.this loop executes till all edges are deleted.
 while(counter<=no_of_edges)
    {
    //mark the truss of the edges with support less than equal to k-2 as k.
    while(MATRIX(edge_sup,ind,1)<=k-2)
       {
       eid=MATRIX(edge_sup,ind,0);
       if((ind+1)<no_of_edges && MATRIX(edge_sup,ind,1)==MATRIX(edge_sup,ind+1,1))
          VECTOR(sindex)[(long int)MATRIX(edge_sup,ind,1)]++;
       else
          VECTOR(sindex)[(long int)MATRIX(edge_sup,ind,1)]=-1;
       
       if(MATRIX(edge_sup,ind,1)==0)
          MATRIX(edge_sup,ind,1)=-1;
       else
          { 
          MATRIX(edge_sup,ind,1)=-1;
          u=IGRAPH_FROM(graph,eid);
          v=IGRAPH_TO(graph,eid); 
          neis1=igraph_adjlist_get(&al,u);
          neis2=igraph_adjlist_get(&al,v);
    
          d1=igraph_vector_int_size(neis1);
          d2=igraph_vector_int_size(neis2);
          w=neis1;
          if(d2<d1)
            {
            temp=u;
            u=v;
            v=temp;
            w=neis2;
            }
          nsize=igraph_vector_int_size(w);
       
          //decrease the support of the other two edges for each triangle whose part is this deleted edge.
          for(j=0;j<nsize;j++)
             {
             igraph_get_eid(graph,&eid2,(igraph_integer_t)VECTOR(*w)[j],v,IGRAPH_UNDIRECTED,0);
             if(eid2!=-1)
               {
               igraph_get_eid(graph,&eid1,(igraph_integer_t)VECTOR(*w)[j],u,IGRAPH_UNDIRECTED,1);
               if(!deleted[eid1] && !deleted[eid2])
                 {
                 //find the edge with id eid1(edge in the triangle) in edge_sup and decrease it's support.
                 ind1=(long int)VECTOR(edges)[eid1];
                 sup1=(long int)MATRIX(edge_sup,ind1,1);
                 MATRIX(edge_sup,ind1,1)=sup1-1;
                
                 //reorder the edge_sup to make it sorted.
                 if((ind1+1 < no_of_edges && MATRIX(edge_sup,ind1+1,1)==sup1 )||MATRIX(edge_sup,ind1-1,1)==sup1)
                   {
                   vsindex=(long int)VECTOR(sindex)[sup1];
                   if(VECTOR(sindex)[sup1-1]==-1)
                       VECTOR(sindex)[sup1-1]=vsindex;  
                   igraph_matrix_swap_rows(&edge_sup,ind1,vsindex);
                   igraph_vector_swap_elements(&edges,(long int)MATRIX(edge_sup,ind1,0),(long int)MATRIX(edge_sup,vsindex,0));
                   VECTOR(sindex)[sup1]++;
                   }
                 else
                   {
                   VECTOR(sindex)[sup1]=-1;
                   if(VECTOR(sindex)[sup1-1]==-1)  
                      VECTOR(sindex)[sup1-1]=ind1;
                   }
                 
                 //find the edge with id eid2(edge in the triangle) in edge_sup and decrease it's support.
                 ind2=(long int)VECTOR(edges)[eid2];
                 sup2=(long int)MATRIX(edge_sup,ind2,1);
                 MATRIX(edge_sup,ind2,1)=sup2-1;
                
                 //reorder the edge_sup to make it sorted.
                 if((ind2+1 < no_of_edges && MATRIX(edge_sup,ind2+1,1)==sup2) || MATRIX(edge_sup,ind2-1,1)==sup2)
                   {
                   vsindex=VECTOR(sindex)[sup2];
                   if(VECTOR(sindex)[sup2-1]==-1)
                       VECTOR(sindex)[sup2-1]=vsindex;  
                   igraph_matrix_swap_rows(&edge_sup,ind2,vsindex);
                   igraph_vector_swap_elements(&edges,(long int)MATRIX(edge_sup,ind2,0),(long int)MATRIX(edge_sup,vsindex,0));
                   VECTOR(sindex)[sup2]++;
                   }
                 else
                   {
                   VECTOR(sindex)[sup2]=-1;
                   if(VECTOR(sindex)[sup2-1]==-1)  
                      VECTOR(sindex)[sup2-1]=ind2;
                   }
              
                } 
            }
       
          }
         }
      
       VECTOR((*truss))[eid]=k;
       deleted[eid]=1;counter++;
       if(ind<no_of_edges-1)
         ind++;
       else 
         break;
       }
    //if no edges are there with support less than equal to k-2 than increase k if edges are still left.
    if(counter<=no_of_edges)
       k=k+1;
     }
 igraph_matrix_destroy(&edge_sup);
 IGRAPH_FINALLY_CLEAN(1);
 igraph_adjlist_destroy(&al);
 igraph_vector_destroy(&edges); 
 igraph_vector_destroy(&sindex);
 igraph_vector_int_destroy(&result);
 IGRAPH_FINALLY_CLEAN(4);    

 igraph_free(deleted);
 IGRAPH_FINALLY_CLEAN(1);    
    return 0;
}
