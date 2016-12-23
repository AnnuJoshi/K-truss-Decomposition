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
#include <R.h>
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

int truss2(const igraph_t *graph, igraph_vector_t *truss) {

 Rprintf("Calculating truss\n");
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
 Rprintf("truss done\n");
    return 0;
}



int dominating_set(const igraph_t *graph,igraph_vector_t *d_set){
  long int no_of_vertices=igraph_vcount(graph);
  igraph_vector_t bit_array;
  igraph_vector_init(d_set,0);
  igraph_vector_t edges;
  igraph_vector_init(&edges,0); 
  igraph_vector_init(&bit_array,no_of_vertices); //for deleting edges of argument graph update no-of-edges
  igraph_vector_null(&bit_array);
  //igraph_vit_t vit1
  igraph_vs_t vs1;
  igraph_adjlist_t al;
  igraph_adjlist_init(graph,&al,IGRAPH_ALL);
  //igraph_vector_int_t *neis1;
  for(long int i=0;i<no_of_vertices;i++){
  //neis1=igraph_adjlist_get(&al,);
  if(VECTOR(bit_array)[i]==0){
   igraph_vector_push_back (d_set,i);
   IGRAPH_CHECK(igraph_neighbors(graph, &edges,i, IGRAPH_ALL));
   int n=igraph_vector_size(&edges);
   VECTOR(bit_array)[i]=1;
   //Rprintf("neighborhoodgraph mein edges %d\n",n);
   
   for(int k=0;k<n;k++)
      VECTOR(bit_array)[(long int)VECTOR(edges)[k]]=1; 
   }

  }



}

int lower_bounding(igraph_t *graph,igraph_vector_t *lowerbound,igraph_t *gnew){
  Rprintf("I am lower bound\n");
  
  igraph_vit_t vit1,vit2,vit3,vit4;
  igraph_vs_t vs1;
  igraph_es_t es1;
  igraph_eit_t eit1,eit2;
  igraph_vector_t dset;
  
  igraph_vector_t edges,truss,tmp,eids,map,map2,extra2;
 
  igraph_vector_t eid,eid2,eid3,eid4; //making neighborhood graph
  igraph_vector_init(&eid,0);
  igraph_vector_init(&map,0);
 
 
  igraph_integer_t u,v,prev,e_id;
   
  int flag=1;
  igraph_vector_init(&eid3,0);
  igraph_vector_init(&map2,0);

  igraph_vector_init(&edges,igraph_ecount(graph)); //for deleting edges of argument graph update no-of-edges
  igraph_vector_null(&edges);

  for(long int i=0;i<igraph_ecount(graph);i++){
    igraph_vector_push_back (&map,i);
  }
 igraph_vector_t extra,extra1;                   //hash to check internal edges
  
 while(flag){

  long int no_of_nodes=igraph_vcount(graph); //no-of-nodes
  dominating_set(graph,&dset);
  igraph_vector_init(&extra,no_of_nodes);
  igraph_vector_init(&extra2,no_of_nodes);
  igraph_vector_init(&extra1,0); 
  igraph_vector_null(&extra);
  igraph_vector_null(&extra2);
 
  int size1=igraph_vector_size(&dset)/2,size2,count=1;
  if(size1)
     {
      size2=igraph_vector_size(&dset)-size1;
      count=2;
     }
  else
  size1++;

  int from=0,to=size1;

 long int no_of_edges=igraph_ecount(graph);
 

 igraph_vector_init(lowerbound,no_of_edges);
 igraph_vector_null(lowerbound);

 igraph_vector_init(&eids,no_of_edges);
 
 igraph_vector_init(&truss,no_of_edges);
 igraph_vector_init(&tmp,no_of_edges);
 
 igraph_vector_init(&eid2,0);

  for(int i=0;i<count;i++){
   
   
   Rprintf("From is %d To is %d\n",from,to);

   while(from<to){//handling internal edges along with creating partitions in extra1
    u=(long int)VECTOR(dset)[from];
    
     VECTOR(extra2)[u]=1;
     igraph_neighbors(graph,&tmp,u,IGRAPH_ALL);
      igraph_vector_push_back (&extra1,u);
     for(long int s=0;s<igraph_vector_size(&tmp);s++){
       if(!VECTOR(extra2)[(long int)VECTOR(tmp)[s]]){
       igraph_vector_push_back (&extra1,(long int)VECTOR(tmp)[s]);
       VECTOR(extra2)[(long int)VECTOR(tmp)[s]]=1;}
     }
    from++;
    igraph_vector_clear (&tmp);
   }//partition created in extra1

    
   

   for(long int s=0;s<igraph_vector_size(&extra1);s++)
   {
    u=(long int)VECTOR(extra1)[s];
    Rprintf("u is %li\n",u);
    VECTOR(extra)[u]=1;
    igraph_neighbors(graph,&tmp,u,IGRAPH_ALL);
     for(long int t=0;t<igraph_vector_size(&tmp);t++)
      { 
       if(!(VECTOR(extra)[(long int)VECTOR(tmp)[t]]))
        {     
        Rprintf("external neighbors of %li is %li\n",u,(long int)VECTOR(tmp)[t]);
        igraph_vector_push_back (&eid,u);
        igraph_vector_push_back (&eid,(long int)VECTOR(tmp)[t]); 
      }
      else
	{
        igraph_get_eid(graph,&e_id,(long int)VECTOR(tmp)[t],u,FALSE, TRUE);
          Rprintf("eid %d\n",e_id);
          //VECTOR(edges)[e_id]=1;
          VECTOR(edges)[(long int)VECTOR(map)[e_id]]=1;
      }   
   }
  
 }
  
  
  igraph_get_eids(graph,&eids,&eid,NULL,FALSE,FALSE); //take eids on basis of the recently constructed edge list from current partition 

  Rprintf("to delete edge ids\n");
  for(long int s=0;s<igraph_vector_size(&map);s++)
         {
    
           Rprintf("%li\n",(long int)VECTOR(edges)[(long int)VECTOR(map)[s]]);
         } 
  
  igraph_t g1; //manage memory properly
  igraph_create(&g1,&eid,0,FALSE);    
   
   Rprintf("edge ids listed\n");
        for(long int s=0;s<igraph_vector_size(&eids);s++)
         {
    
           igraph_edge(graph,VECTOR(eids)[s],&u, &v);
           Rprintf("%li %li %li\n",(long int)u,(long int)v,(long int)VECTOR(eids)[s]);
         }
     
     truss2(&g1,&truss);
        
     long int size= igraph_vector_size(&eids);
     if( igraph_vector_size(&eids)> igraph_vector_size(&map))
     size= igraph_vector_size(&map);
     
     for(long int j=0;j<size;j++)
       {
         if((long int)VECTOR(truss)[j]>VECTOR(*lowerbound)[(long int)VECTOR(map)[(long int)VECTOR(eids)[j]]])
         VECTOR(*lowerbound)[(long int)VECTOR(map)[(long int)VECTOR(eids)[j]]]=(long int)VECTOR(truss)[j];

         if(VECTOR(*lowerbound)[(long int)VECTOR(map)[(long int)VECTOR(eids)[j]]]==2 && VECTOR(edges)[(long int)VECTOR(map)[(long int)VECTOR(eids)[j]]])
         VECTOR(edges)[(long int)VECTOR(map)[(long int)VECTOR(eids)[j]]]=2;

         Rprintf("%li for edge %li",(long int)VECTOR(*lowerbound)[(long int)VECTOR(map)[(long int)VECTOR(eids)[j]]],(long int)VECTOR(map)[(long int)VECTOR(eids)[j]]);
        }
    
    
    igraph_vector_clear (&eid);
   igraph_vector_clear (&extra1); 
   igraph_vector_null(&extra);

   igraph_vector_null(&extra2);
   //from+=size1;
   to+=size2;   
  }//for main
  
 
   
  /*for(long int i=0;i< igraph_vector_size(&edges);i++){
   igraph_edge(graph,i,&u, &v);//edge between u and v
   if(VECTOR(edges)[i]==1)//to be removed internal edges
     {
       igraph_vector_push_back (&eid3,u);
       igraph_vector_push_back (&eid3,v); 
     }
    else if(VECTOR(edges)[i]==2){
        
     }
    else{
       igraph_vector_push_back (&eid2,u);
       igraph_vector_push_back (&eid2,v);
     }
    //Rprintf("%li %li\n",i,(long int)VECTOR(edges)[i]); //problemo
   }*/

  for(long int i=0;i< igraph_vector_size(&map);i++){
   igraph_edge(graph,i,&u, &v);//edge between u and v
   if(VECTOR(edges)[(long int)VECTOR(map)[i]]==1)//to be removed internal edges
     {
       igraph_vector_push_back (&eid3,u);
       igraph_vector_push_back (&eid3,v); 
     }
    else if(VECTOR(edges)[(long int)VECTOR(map)[i]]==2){
        
     }
    else{
       igraph_vector_push_back (&eid2,u);
       igraph_vector_push_back (&eid2,v);
       igraph_vector_push_back (&map2,(long int)VECTOR(map)[i]);
     }
    //Rprintf("%li %li\n",i,(long int)VECTOR(edges)[i]); //problemo
   }
  //igraph_vector_clear (&map);

 /* for(long int i=0;i< igraph_vector_size(&map2);i++)
   igraph_vector_push_back (&map,(long int)VECTOR(map2)[i]);

  igraph_vector_clear (&map2);
*/
  //if(igraph_vector_size(&eid2)==0)
    flag=0;
  
  Rprintf("\n%li %li\n",igraph_vector_size(&eid2),igraph_vector_size(&eid3)); 
  igraph_create(graph,&eid2,0,FALSE);

  }//while

  igraph_create(gnew,&eid3,0,FALSE);  
   

 return 0;   
}//lower



int bottom_up_truss(igraph_t *graph){
  long int k=3;
  Rprintf("hi bottom_up\n");
  igraph_integer_t u,v;
  igraph_vector_t lowerbound,candidate,extra,tmp,eid,map,deleted_edges;
  igraph_t gnew;
  igraph_vector_init(&lowerbound,igraph_ecount(graph));
   igraph_vector_init(&candidate,0);
  lower_bounding(graph,&lowerbound,&gnew);
 
  /*for(long int i=0;i<igraph_vector_size(&lowerbound);i++){

   Rprintf("%li\n",(long int)VECTOR(lowerbound)[i]);
   
  }*/
 
  igraph_vector_init(&extra,igraph_vcount(&gnew));
  igraph_vector_init(&tmp,0);
  igraph_vector_init(&eid,0);
  igraph_vector_init(&map,0);//for maintaining mapping with original

  igraph_vector_null(&extra);
  long int no_of_edges=igraph_ecount(&gnew);
  igraph_vector_init(&deleted_edges,no_of_edges); //deleted edges mark
  igraph_vector_null(&deleted_edges);

  long int flag=1;  

  /*while(flag){

   //candidate graph
   for(long int i=0;i<no_of_edges;i++){
   if((long int)VECTOR(lowerbound)[i]<=k && (long int)VECTOR(lowerbound)[i]>2){
   igraph_edge(&gnew,i,&u, &v);//edge between u and v
       igraph_vector_push_back (&candidate,v); //one vertex
       igraph_vector_push_back (&map,i); //edge id in map
     }
  }//for

  if(igraph_vector_size(&candidate)){
  for(long int s=0;s<igraph_vector_size(&candidate);s++)
   {
    u=(long int)VECTOR(candidate)[s];
    Rprintf("u is %li\n",u);
    VECTOR(extra)[u]=1;
    igraph_neighbors(gnew,&tmp,u,IGRAPH_ALL);
     for(long int t=0;t<igraph_vector_size(&tmp);t++)
      { 
       if(!(VECTOR(extra)[(long int)VECTOR(tmp)[t]]))
        {     
        //Rprintf("external neighbors of %li is %li\n",u,(long int)VECTOR(tmp)[t]);
        igraph_vector_push_back (&eid,u);
        igraph_vector_push_back (&eid,(long int)VECTOR(tmp)[t]); 
      }
      else
	{
        igraph_get_eid(&gnew,&e_id,(long int)VECTOR(tmp)[t],u,FALSE, TRUE);
          VECTOR(edges)[(long int)VECTOR(map)[e_id]]=1;
      }
   igraph_vector_clear (&tmp);   
   }
  }//if

   if(igraph_vector_size(&eid2)==0)
    flag=0;

   igraph_vector_clear (&eid);
   igraph_vector_clear (&candidate);
   igraph_vector_clear (&map); 
   igraph_vector_null(&extra);
  }//while*/

}




int igraph_trussness(const igraph_t *graph, igraph_vector_t *truss) {

  Rprintf("Hello truss\n");
 
  bottom_up_truss(graph);
    return 0;
}
