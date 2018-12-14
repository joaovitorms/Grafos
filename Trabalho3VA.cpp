#include <math.h>
#include <stdlib.h>
#include <stdio.h>
#include <conio.h>
#include <sys/types.h>
#include <time.h>
#define MaxDim 100
#define Rand_Max 10000

int find( int );
void ffunion( int , int );
void seedRandom(unsigned int );
double randomn(void );
double seconds(void );
void gera_grafo(int , double);
void gera_grafo_sim(int , double);
void print_grafo(int );
void print_listas(int );
void constroi_lista(int );
void alcance(int, int);
void print_alcance(void);
void init_buscaP(void);
void buscaP(int );
void print_alc_buscaP(int );
void FordBellman(int );
void Prim(int );
void Dijkstra(int );
void Kruskal(void  );
void Boruvka(int );
void AGM_buscaP( int , int );
void print_listas_AGM_B(int , int , int* );
// Variáveis Globais
int MAdj[MaxDim][MaxDim];
int Dist[MaxDim][MaxDim];
int LisAdjP[MaxDim][MaxDim];
int LisAdjN[MaxDim][MaxDim];
int CardP[MaxDim];
int CardN[MaxDim];
int M_arcos; // Numero de Arcos no Grafo
int I_arco[MaxDim*MaxDim]; //  I_arco[k] Inicio(Origem) do Arco k
int J_arco[MaxDim*MaxDim]; //  J_arco[k] Fim(Destino) do Arco k
int Hq, Tq;
int Dim;
int Q[MaxDim];
int mark[MaxDim];
int DistInfinita;
int AGM_LisAdjP[MaxDim][MaxDim];
int AGM_CardP[MaxDim];

main()
{
	int v,a;
	float  faux;
	double dens;

	printf(" Digite o numero de vertices no grafo: ");
	scanf("%d", &Dim);
	printf(" Digite a densidade o grafo: ");
	scanf("%f", &faux);
	dens = faux;
	gera_grafo(Dim, dens);
	constroi_lista (Dim);
	print_grafo(Dim);
	print_listas(Dim);
	printf(" Boruvka \n");
    Boruvka( Dim );
	return(0);
}

//funções e procedimentos

void Boruvka(int n)
{
     int i, j, p, ii, jj, iter, n_grupos;
     int grupo[MaxDim], minDist[MaxDim], minArco[MaxDim];
     int arco_usado[MaxDim*MaxDim];
       
     printf("\n n=%d Numero de arcos=%d \n", n, M_arcos);
     for(i=1; i<=n; i++)
     {
       grupo[i] = i;
       AGM_CardP[i] = 0;
     }
     for(i=1; i<=M_arcos; i++)
     {
       arco_usado[i] = 0;
     }
     n_grupos = n;

     iter = 0;
     print_listas_AGM_B( n, iter, grupo);

     
     do
     {
       iter++;
           for(i=1; i<=n_grupos; i++)
       {
         minDist[i]=DistInfinita;
       }
       
           for(j=1; j<=M_arcos; j++)
       {
          ii = I_arco[j]; jj = J_arco[j];
          if (grupo[ii] != grupo[jj])
          {
             if ( Dist[ii][jj] < minDist[grupo[ii]])
             {
                  minDist[grupo[ii]] = Dist[ii][jj];
                  minArco[grupo[ii]] = j;
             }
             if ( Dist[ii][jj] < minDist[grupo[jj]])
             {
                  minDist[grupo[jj]] = Dist[ii][jj];
                  minArco[grupo[jj]] = j;
             }
          }
       }
           for (ii=1; ii<=n_grupos; ii++)
       {
           jj = minArco[ii];
           if (arco_usado[jj] == 0) 
           {
            arco_usado[jj] = 1;
            
            i = I_arco[jj]; j = J_arco[jj];
			p = AGM_CardP[i] + 1;
			AGM_LisAdjP[i][p] = j;
			AGM_CardP[i] = p;
			p = AGM_CardP[j] + 1;
            AGM_LisAdjP[j][p] = i;
			AGM_CardP[j] = p;
           }
       }
                           
       for (i=1; i<=n; i++)
       {
           mark[i] = 0;
       }
       
       n_grupos = 0;
       for (i=1; i<=n; i++)
       {
           if (mark[i] == 0)
           {
               n_grupos++;
               AGM_buscaP( i, n_grupos );
           }
       }       
       
       for (i=1; i<=n; i++)
       {
           grupo[i] = mark[i];
       }

       print_listas_AGM_B( n, iter, grupo);
       
     }
     while (n_grupos > 1);
}


void AGM_buscaP( int v, int rotulo)
{
     int card, w, i;
     
     card = AGM_CardP[v];
     for (i=1; i<=card; i++)
     {
		 w = AGM_LisAdjP[v][i];
         if (mark[w] == 0)
         {
             mark[w] = rotulo;
             AGM_buscaP(w, rotulo);
         }
     }
}

void print_listas_AGM_B(int n, int iter, int grupo[])
{
	int i,j, p;
	printf("\n Boruvka - Floresta Iter %d - Listas de Adjacencia\n", iter);
	for(i=1; i<=n; i++)
	{
		printf("%d | Grupo %d | %d Arcos Saindo : ", i, grupo[i], AGM_CardP[i]);
		p = AGM_CardP[i];
		for(j=1; j<=p; j++)
		{
			printf(" %d ",AGM_LisAdjP[i][j]);
		}
		printf("\n");
	}
	printf("\n");
}


void Dijkstra(int s)
{
	int v,w,k,l, vmin, dmin;
	int d_temp[MaxDim];
	int pred[MaxDim];
	int pos_prox[MaxDim];


	for (v=1; v<=Dim; v++)
	{
		d_temp[v] = DistInfinita;
		pos_prox[v] = 0;
		pred[v] = -1;
	}


	d_temp[s] = 0;
	pred[s] = 0;

	k = 1;
	pos_prox[s] = k;


	for(l=1; l<=CardP[s]; l++)
	{
		v = LisAdjP[s][l];
		if (d_temp[v] > d_temp[s]+Dist[s][v])
		{
           d_temp[v] = d_temp[s]+Dist[s][v];
		   pred[v] = s;
		}
	}


    for (k=2; k<=Dim; k++)
	{
	   vmin = 0;
	   dmin = DistInfinita;
       for (v=1; v<=Dim; v++)
	   {
		   if ((d_temp[v] < dmin) && (pos_prox[v] == 0))
		   {
               vmin = v;
               dmin = d_temp[v];
		   }
	   }
       printf(" Vmin: %d  DistMin: %d\n", vmin, dmin);

	   pos_prox[vmin] = k;

   	  for(l=1; l<=CardP[vmin]; l++)
	  {
	 	 v = LisAdjP[vmin][l];
		 if ( (pos_prox[v] == 0) && (d_temp[v] > d_temp[vmin] + Dist[vmin][v])) 
		 {
            d_temp[v] = d_temp[vmin] + Dist[vmin][v]; 
		    pred[v] = vmin;
		 }
	  }

	}

	printf(" DIJKSTRA -- CMC a partir de %d \n",s);
	for (v=1; v<=Dim; v++)
	{
		printf(" %d D=%d %d-esimo mais proximo Caminho: ",
			v, d_temp[v], pos_prox[v]);
		w = v;
		while (pred[w] > 0)
		{
			printf(" %d ",pred[w]);
			w = pred[w];
		}
		printf("\n");
	}

	for (v=1; v<=Dim; v++)
	{
			printf("Aresta: %d %d %d\n",v ,pred[v], Dist[v][pred[v]]);
    }

}
void Prim(int s)
{
	int v,w,k,l, vmin, dmin;
	int d_temp[MaxDim];
	int pred[MaxDim];
	int pos_prox[MaxDim];
	for (v=1; v<=Dim; v++)
	{
		d_temp[v] = DistInfinita;
		pos_prox[v] = 0;
		pred[v] = -1;
	}


	d_temp[s] = 0;
	pred[s] = s;

	k = 1;
	pos_prox[s] = k;


	for(l=1; l<=CardP[s]; l++)
	{
		v = LisAdjP[s][l];
		if (d_temp[v] > Dist[s][v]) 
		{
           d_temp[v] = Dist[s][v];
		   pred[v] = s;
		}
	}


    for (k=2; k<=Dim; k++)
	{

	   vmin = 0;
	   dmin = DistInfinita;
       for (v=1; v<=Dim; v++)
	   {
		   if ((d_temp[v] < dmin) && (pos_prox[v] == 0))
		   {
               vmin = v;
               dmin = d_temp[v];
		   }
	   }


       printf(" Vmin: %d  DistMin: %d\n", vmin, dmin);

	   pos_prox[vmin] = k;


   	  for(l=1; l<=CardP[vmin]; l++)
	  {
	 	 v = LisAdjP[vmin][l];
		 if ( (pos_prox[v] == 0) && (d_temp[v] > Dist[vmin][v])) 
		 {
            d_temp[v] = Dist[vmin][v]; 
		    pred[v] = vmin;
		 }
	  }

	}

	for (v=1; v<=Dim; v++)
	{
			printf("Aresta: %d %d %d\n",v ,pred[v], Dist[v][pred[v]]);
    }

}

int pont[MaxDim];
int rank[MaxDim];

int find(int v)
{
    if ( pont[v] != v)
    {
         return( find(pont[v]) );
    }
    return(v);
}

void ffunion( int c1, int c2 )
{
   if (rank[c1] < rank[c2])
   {
       pont[c1] = c2;
   }
   else
   {
       pont[c2] = c1;
       if ( rank[c1] == rank[c2] )
       {
            rank[c1]++;
       }
   }
}


void Kruskal( )
{
	int v,w,k, ll;
	int v1, v2, w1, w2, c1, c2;
	int temp;
	int pred[MaxDim];
	int ind_sort[MaxDim*MaxDim];

	printf(" Kruskal MST  01 \n");

	for (v=1; v<=Dim; v++)
	{
		pont[v] = v;
		rank[v] = 0;
	}
	printf(" Kruskal MST 02 \n");

    for (k=1; k<=M_arcos; k++)
	{
        ind_sort[k] = k;
    }
    for (ll=1; ll<=M_arcos; ll++)
	{
		for(k=1; k<=M_arcos-1; k++)
		{
            v1 = I_arco[ind_sort[k]];
            w1 = J_arco[ind_sort[k]];
            v2 = I_arco[ind_sort[k+1]];
            w2 = J_arco[ind_sort[k+1]];
			if( Dist[v1][w1] > Dist[v2][w2] )
			{
                temp = ind_sort[k];
                ind_sort[k] = ind_sort[k+1];
                ind_sort[k+1] = temp;
			}
		}
	}
	printf(" Kruskal MST \n");

    for (k=1; k<=M_arcos - 1; k++)
	{
         v = I_arco[ind_sort[k]];
         w = J_arco[ind_sort[k]];
         printf(" A %d  %d  %d\n", v, w, Dist[v][w]);


         c1 = find(v);
         c2 = find(w);

         if (c1 != c2)
         {
                printf(" Aresta %d  %d  %d\n", v, w, Dist[v][w]);
                ffunion(c1,c2);
         }
     }

}

void FordBellman(int s)
{
	int v,w,k, ll;
	int d_temp[MaxDim];
	int pred[MaxDim];
	int circ_neg;

	circ_neg = 0;
	for (v=1; v<=Dim; v++)
	{
		d_temp[v] = DistInfinita;
		pred[v] = -1;
	}

	d_temp[s] = 0;
	pred[s] = 0;
    for (k=1; k<=Dim - 1; k++)
	{

		for(ll=1; ll<=M_arcos; ll++)
		{
			v = I_arco[ll];
			w = J_arco[ll];
			if( d_temp[ v ] +  Dist[v][w] < d_temp[w] )
			{
				d_temp[w] = d_temp[ v ] +  Dist[v][w];
				pred[w] = v;
			}
		}
	    for (v=1; v<=Dim; v++)
        {
		   printf(" %d D=%d Caminho: ",v, d_temp[v]);
		   w = v;
	       printf("\n");
        }
        getch();


	}

        getch();
	for(ll=1; ll<=M_arcos; ll++)
	{
			v = I_arco[ll];
			w = J_arco[ll];
			if( d_temp[ v ] +  Dist[v][w] < d_temp[w] )
			{
				d_temp[w] = d_temp[ v ] +  Dist[v][w];
				pred[w] = v;
				printf(" CIRCUITO NEGATIVO DETECTADO\n");
				circ_neg=1;
				w=v;
				do{
                    printf("ant v=%d w=%d \n",v,w);
					printf(" %d ",w);
					w = pred[w];
                    printf("dep v=%d w=%d \n",v,w);
                    getch();
				}
				while(w != v);
				printf(" \n\n ");

			}
	}


    if(circ_neg == 0)
	{
	printf(" Ford Bellman -- CMC a partir de %d \n",s);
	for (v=1; v<=Dim; v++)
	{
		printf(" %d D=%d Caminho: ",v, d_temp[v]);
		w = v;
		while (pred[w] > 0)
		{
			printf(" %d ",pred[w]);
			w = pred[w];
		}
		printf("\n");
	}
	}

}

void print_alc_buscaP(int v)
{
	int i;
		printf("\n Vertices alcancaveis a partir de %d \n",v);

		for (i=1;i<=Dim;i++)
		{
			if( mark[i] == 1)
			{
				printf(" %d ",i);
			}
		}
		printf(" \n");
}

void init_buscaP()
{
	int i;
		for (i=1;i<=Dim;i++)
		{
			mark[i] = 0;
		}

		printf("\n Busca em Profundidade INICIADA \n");

}

void buscaP(int v)
{
	int w,i;

    printf("%d \n",v);

	if (mark[v] == 0)
	{
		mark[v] = 1;
		for (i=1;i<=CardP[v];i++)
		{
			w=LisAdjP[v][i];
            printf("(%d,%d)",v,w);
			buscaP(w);
		}
	}
}


void print_alcance(void){
	int i;
	printf("Os vertices atingidos sao:\n");
	for(i=1;i<=Tq;i++){
		printf(" %d ", Q[i]);
	}
	printf("\n");
}

void alcance(int v, int n){
	int u,i,k,j,w,I,F;
	for(i=1;i<=n;i++) mark[i]=-1;

	Q[1]=v;
	Hq=1;
	Tq=1;
	mark[v]=0;


	for(k=1;k<=n;k++){
        printf(" Dist: %d %d \n",k,n);

		I=Hq;
		F=Tq;    
		for (j=I;j<=F;j++){
		            
			w=Q[j]; 
			        
			for (i=1;i<=CardP[w];i++){
				u=LisAdjP[w][i]; 
				if (mark[u]==-1){
					mark[u]=k;

					printf("%d ",u);

					Q[++Tq]=u;
				}
			}
		}
		Hq=F+1;

        printf("\n");


	}
}


void gera_grafo(int n, double dens)
{
	int i,j;

	M_arcos = 0;
	DistInfinita = 1;
	printf("\n\n Gerando Grafo Aleatorio de Densidade: %f #Vertices: %d\n\n",dens,n);
	for(i=1; i<=n; i++)
	{
		for(j=1; j<=n; j++)
		{
		  if(i != j)
		  {
            if(randomn() < dens)
			{
				M_arcos++;
				I_arco[M_arcos] = i;
				J_arco[M_arcos] = j;
				MAdj[i][j]=1;
				Dist[i][j]=  600 - (int)(randomn() * 1000.);
		        DistInfinita += Dist[i][j];
			}
			else
			{
				MAdj[i][j]=0;
			}
          }
          else
          {
			MAdj[i][j]=0;
          }
		}
	}

	for(i=1; i<=n; i++)
	{
		for(j=1; j<=n; j++)
		{
			if(MAdj[i][j]==0)
			{
				Dist[i][j]=DistInfinita;
			}
		}
	}

}


void gera_grafo_sim(int n, double dens)
{
	int i,j;

	M_arcos = 0;
	DistInfinita = 1;
	printf("\n\n Gerando Grafo Aleatorio de Densidade: %f #Vertices: %d\n\n",dens,n);
	for(i=1; i<=n; i++)
	{
		for(j=i; j<=n; j++)
		{
            if(i != j)
            {
			    if(randomn() < dens)
			    {
				   M_arcos++;
				   I_arco[M_arcos] = i;
				   J_arco[M_arcos] = j;
				   MAdj[i][j]=1;
				   MAdj[j][i]=1;

				   Dist[i][j]= (int)(randomn() * 1000.);
				   Dist[j][i]= Dist[i][j];

				   DistInfinita += Dist[i][j];
                 }
				 else
			     {
				   MAdj[i][j]=0;
				   MAdj[j][i]=0;
			     }
              }
              else
			  {
				 MAdj[i][j]=0;
				 MAdj[j][i]=0;
			  }
        }
    }


	for(i=1; i<=n; i++)
	{
		for(j=i; j<=n; j++)
		{
			if(MAdj[i][j]==0)
			{
				Dist[i][j]=DistInfinita;
				Dist[j][i]=DistInfinita;
			}
		}
	}

}
void print_grafo(int n)
{
	int i,j;
	printf("\n GRAFO: Matriz de Adjacencia\n");
	for(i=1; i<=n; i++)
	{
		for(j=1; j<=n; j++)
		{
			printf("%d:%d %d ",i,j,MAdj[i][j]);
		}
		printf("\n");
	}
	printf("\n");
	for(i=1; i<=n; i++)
	{
		for(j=1; j<=n; j++)
		{
			printf("%d:%d %d ",i,j,Dist[i][j]);
		}
		printf("\n");
	}
	printf("\n");
}
void  constroi_lista(int n)
{
	int i,j,p;

	for (i=1; i<=n; i++)
	{
		CardP[i] = 0;
		CardN[i] = 0;
	}

	for(i=1; i<=n; i++)
	{
		for(j=1; j<=n; j++)
		{
			if (MAdj[i][j] == 1)
			{
				p = CardP[i] + 1;
				LisAdjP[i][p] = j;
				CardP[i] = p;

				p = CardN[j] + 1;
				LisAdjN[j][p] = i;
				CardN[j] = p;
			}
		}
	}

}
void print_listas(int n)
{
	int i,j, p, sum;
	sum = 0;
	printf("\n GRAFO: Listas de Adjacencia\n");
	printf("\n  Listas de Saida de Arcos \n");
	for(i=1; i<=n; i++)
	{
		printf("%d | %d Arcos Saindo : ", i, CardP[i]);
		p = CardP[i];
		for(j=1; j<=p; j++)
		{
			printf(" %d ",LisAdjP[i][j]);
		}
		printf("\n");
	}
	printf("\n  Listas de Entrada de Arcos \n");
	for(i=1; i<=n; i++)
	{
		printf("%d | %d Arcos Chegando : ", i, CardN[i]);
		p = CardN[i];
		for(j=1; j<=p; j++)
		{
			printf(" %d ",LisAdjN[i][j]);
		}
		printf("\n");
	}
	printf("\n");
}

void seedRandom(unsigned int seed)
{
  srand(seed);
  return;
}

double randomn(void)
{
  double rrr;

  rrr = (double) rand() / (double) RAND_MAX;
  return rrr;
}

double seconds()

{
  double secs;

  secs = (double)(clock() / 1000.0);
  return(secs);
}

