#include <iostream>
#include <fstream>
#include <cmath>
#include <sstream>
#include <bitset>
#include <vector>
#include <string>
using namespace std;
typedef short int uint;
typedef unsigned long long int ullint;
//Maximum
const unsigned int MAX_2N=22,MAX_N=11, MAX_CYC = 1100,MAX_2P2=1000,MAX_C = 10000, MAXT = 100000;
//Functions
int NumCyEv(int p);
bool Itir(int, int, int, int, const int);
bool Filtre(int, int, int, uint*, uint*, uint*, int, const int);
bool PermuteFiltre(int, int, uint*, uint*, uint*, int, int, const int);
void Distrib(int, int, const int);
void CycGen(const int);
int Init(int, const int);
inline bool Equal(uint*,uint*, int);
inline bool Mini(uint*, uint*, const int);
inline void ADD(uint *L1, uint *L2, int);
inline void recswap(int, int, uint*, uint*);
inline void REV(int, int, uint*, uint*);
inline void FindR(int, int, uint*, uint*);
inline void Swap(uint*, uint*, int, int);
bool irreducible(uint *L, uint *R, const int n);
bool oriArrBr[MAX_N][MAX_N] = {{false}}, oriArrCh[MAX_N][MAX_2N] = {{false}};
void PropreLabel(uint *L, uint *R, uint *PosL, uint *PosR, const int n);
void SortBit2D(const vector< vector<ullint> > &vec2D, unsigned int b, unsigned int be, unsigned int en);
void Sort2D(const vector< vector<ullint> > &vec2D);
void Sort(ullint * A, ullint * B, unsigned int n);
unsigned int countSetBits0(ullint n);
unsigned int countSetBits(ullint n,int p);
int ToN(ullint n);
void WriteUint(string st, vector< vector<ullint> > Mat);
void WriteInt(string st, vector< vector<int> > Mat);
void DFSUtil(int v, bool visited[], uint *L, uint *R);
inline void AddToFillLR(uint *L, uint *R, const int n);
void organizeAndWrite(int n);
bool evalCycle(ullint CY,const int n);
bool validCycle(ullint CY,const int n);
void combining(int m, int t, int n);
void edgCoef();
void buildEq();
void genCycles(ullint tr, int n);
bool fraction(ullint tr, int n);
bool decompression(ullint p, int n);
bool spanTrees(ullint *tt,int k, int n);
void initialiseLabel(int n);
//Global variables
uint L[MAX_N], R[MAX_N], PosL[MAX_N], tpL[MAX_N], tpR[MAX_N], tpPosL[MAX_N],tpPosR[MAX_N],Lc[MAX_N],Lc0[MAX_N],PosR[MAX_N];
int PosL0[MAX_N]= {0}, PosR0[MAX_N]= {0}, L0[MAX_N] = {0}, R0[MAX_N] = {0};
ullint edjTF[MAX_N][MAX_N] = {{0}}, tt[MAX_N]= {0}, Lb[MAX_N][MAX_N]= {0};
static ullint ATr = 0;
int sz[MAX_N]= {1};
ullint Den[MAX_N]= {0}, DenF[MAX_N]= {0}, Den0[MAX_N]= {0}, Nig[MAX_N]= {0}, NigF[MAX_N]= {0}; //Initialize denominators
int br[MAX_2N][MAX_2N]= {0}, Posbr[MAX_2N][MAX_2N]= {{0}}, nt[MAX_2N]= {0}; //The nail vertex of each leaf of nt
ullint noneb = 0, Ptt = 0;//n bits taking the value 1 bit or 00000....001111...11
ullint tp[4][MAX_N], Cir[MAX_N] = {0}, F[MAX_N] = {0}, S[MAX_C], PairEdg[2*MAX_N]= {0}, Sr[MAX_C];//Fundamental circuits
int szS = 1, nEq = 1, dn = 1, szSr=1;
int NumC[2*MAX_N]= {0},szEdg[MAX_C]= {0},MatFin[MAX_C]= {0},MatFinR[MAX_C]= {0},CycNum[MAX_C][2*MAX_N]= {0},CycNumR[MAX_C][2*MAX_N]= {0},LPQ[2*MAX_N]= {1},c[100]= {0},szEdgR[MAX_C]= {0};
short int MatEq[MAX_C][2*MAX_N] = {0};//For building equations
vector< vector<ullint>> matNom, matSignNom, matDen, matSignDen;
vector< vector<int>> matCoefNom;
vector<int> Pos, posZero, posOne;
vector<ullint>  bitOne, bitZero;
int tSym;
int nDe = 0;
int nNe = 0;
int maxSzTree = 0;
uint LisGenDet[MAX_N], LisSizDet[MAX_N], Matbeg[MAX_N];
uint tpLk[MAX_N][MAX_N], tpLck[MAX_N][MAX_N], tpPosLk[MAX_N][MAX_N];
uint FIL[MAX_CYC][MAX_N]= {0}, CFIL[MAX_CYC][MAX_N]= {0},Indx[MAX_CYC][MAX_N]= {0};
uint lnc[MAX_CYC]= {0};
uint Dsz[MAX_CYC][MAX_N]= {0}, Hsz[MAX_CYC][MAX_N]= {0};
uint MatS[MAX_2P2][MAX_N], PosMatS[MAX_2P2][MAX_N] = {{0}};
unsigned long long int CycBitF[MAX_2P2][MAX_2N] = {0};
int szCB[MAX_2P2] = {0};
int ic[MAX_N], jc[MAX_N];
static int LN = 0, v = 0, dv = 1, dvc = 1;
ullint tde=0;
static bool syy = false;
uint VrtxDFS[MAX_N] = {0}, PosVrtxDFS[MAX_N] = {0};
static int jdfs = 1;
int Cyc[MAX_N][MAX_N] = {0};
int szCyc[MAX_N] = {0};
int sztC = 0;
uint cyL[MAX_N] = {0}, cyR[MAX_N] = {0}, cyPosL[MAX_N] = {0}, cyPosR[MAX_N] = {0}, cyLR[MAX_2N] = {0}, PosLR[MAX_2N] = {0}, cyLR0[MAX_2N] = {0};
int numbCy[MAX_N] = {0};
int TotD = 0;
int irrOnly = 2;
uint branches[MAX_N][MAX_N], chords[MAX_N][MAX_2N], degVrtx[MAX_N] = {0};
ofstream myfile, myfilec, tex;

void SortBit2D(const vector< vector<ullint> > &vec2D, unsigned int b, unsigned int be, unsigned int en)
{
    unsigned int i = 0, k = 0, nOne = 0, nZero = 0;
    vector<ullint> tVec;
    vector<int>  tPos;
    for(i = be; i<en; i++)
    {
        tVec.push_back(vec2D[Pos[i]][b]);//Point to first element to organize from this
        tPos.push_back(Pos[i]);
    }
    for(k = 0; k<dn; k++)
    {
        nOne = 0;
        nZero = 0;
        for(i = 0; i<tVec.size(); i++)
        {
            if(tVec[i]&(1<<k))
            {
                bitOne[nOne] = tVec[i];
                posOne[nOne] = tPos[i];
                nOne++;
            }
            else
            {
                bitZero[nZero] = tVec[i];
                posZero[nZero] = tPos[i];
                nZero++;
            }
        }
        for(i = 0; i<nZero; i++)
        {
            tVec[i] = bitZero[i];
            tPos[i] = posZero[i];
        }
        for(i = 0; i<nOne; i++)
        {
            tVec[nZero+i] = bitOne[i];
            tPos[nZero+i] = posOne[i];
        }
    }
    for(i = be; i<en; i++)
        Pos[i] = tPos[i-be];
    int r = 0;
    i = 1+be;
    while(i<en)
    {
        if(vec2D[Pos[i]][b]!=vec2D[Pos[be]][b])
        {
            if(r>0)
                SortBit2D(vec2D,b+1,be,i);
            be = i;
            r = 0;
        }
        else
            r++;
        if(r==en-be-1)
        {
            if(r>0)
                SortBit2D(vec2D,b+1,be,en);
            r = 0;
        }
        i++;
    }
}

void Sort2D(const vector< vector<ullint> > &vec2D)
{
    if(!Pos.empty())
        Pos.clear();

    for(unsigned int i = 0; i<vec2D.size(); i++)
        Pos.push_back(i);

    SortBit2D(vec2D,0,0,vec2D.size());
}

void Sort(ullint * A, ullint * B, unsigned int n)
{
    for(unsigned int i = 1; i<n-1; i++)
        for(unsigned int j = i+1; j<n; j++)
            if(A[i]>A[j])
            {
                swap(A[i], A[j]);
                swap(B[i], B[j]);
            }
}

unsigned int countSetBits0(ullint n)
{
    unsigned int cn = 0;
    while (n)
    {
        n^=n&~(n-1);
        cn++;
    }
    return cn;
}

unsigned int countSetBits(ullint n,int p)
{
    unsigned int cn = 0;
    while (n)
    {
        Lb[p][cn]=n&~(n-1) ;
        n^=Lb[p][cn];
        cn++;
    }
    return cn;
}

int ToN(ullint n)
{
    int nb = 0;
    while(n)
    {
        nb++;
        n>>=1;
    };
    return nb;
}

void WriteUint(string st, vector< vector<ullint> > Mat)
{
    myfile<<st<<"{";
    for(int kk=0; kk<Mat.size(); kk++)
    {
        myfile<<"{";
        for(int i=0; i<Mat[kk].size(); i++)
        {
            myfile<<Mat[kk][i];
            if(i!=Mat[kk].size()-1)
                myfile<<",";
        }
        if(kk==Mat.size()-1)
            myfile<<"}";
        else
            myfile<<"},";
    }
    myfile<<"},";
}

void WriteInt(string st, vector< vector<int> > Mat)
{
    myfile<<st<<"{";
    for(int kk=0; kk<Mat.size(); kk++)
    {
        myfile<<"{";
        for(int i=0; i<Mat[kk].size(); i++)
        {
            myfile<<Mat[kk][i];
            if(i!=Mat[kk].size()-1)
                myfile<<",";
        }
        if(kk==Mat.size()-1)
            myfile<<"}";
        else
            myfile<<"},";
    }
    myfile<<"},";
}

void DFSUtil(int v, bool visited[], uint *L, uint *R)
{
    visited[v] = true;
    VrtxDFS[jdfs] = v;
    jdfs++;
    if(!visited[L[v]])
        DFSUtil(L[v], visited,L,R);
    if(!visited[R[v]])
        DFSUtil(R[v], visited,L,R);
}

inline void AddToFillLR(uint *L, uint *R, const int n)
{
    myfile<<"{";
    for(int k=1; k<n; k++)
        myfile<<L[k]<<","<<R[k]<<",";
    myfile<<L[n]<<","<<R[n]<<"}";
}

void organizeAndWrite(int n)
{
    vector< vector<ullint>> matNomF, matSignNomF, matDenF, matSignDenF;
    vector< vector<int>> matCoefNomF;
    Sort2D(matDen);//Sorting Integer in increasing order
    int szDD = matDen.size();
    matNomF.resize(szDD);
    matSignNomF.resize(szDD);
    matCoefNomF.resize(szDD);
    int prv = 0, sg = 1, r =0;
    matDenF.push_back(matDen[Pos[0]]);
    matSignDenF.push_back(matSignDen[Pos[0]]);
    matNomF[0].push_back(matNom[Pos[0]][0]);
    matSignNomF[0].push_back(matSignNom[Pos[0]][0]);
    matCoefNomF[0].push_back(matCoefNom[Pos[0]][0]);
    for(int i = 1; i<szDD; i++)
    {
        if(matDen[Pos[i]] != matDen[Pos[i-1]])
        {
            matDenF.push_back(matDen[Pos[i]]);
            matSignDenF.push_back(matSignDen[Pos[i]]);
            prv++;
            r = 0;
        }
        else
        {
            sg = 1;
            for(int j = 0; j<n-1; j++)
                if(matSignDen[Pos[i]][j]!=matSignDen[Pos[i-r-1]][j])
                    sg = -sg;
            matCoefNom[Pos[i]][0] = sg;
            r++;
        }

        matNomF[prv].push_back(matNom[Pos[i]][0]);
        matSignNomF[prv].push_back(matSignNom[Pos[i]][0]);
        matCoefNomF[prv].push_back(matCoefNom[Pos[i]][0]);
    }
    matNomF.resize(prv+1);
    matSignNomF.resize(prv+1);
    matCoefNomF.resize(prv+1);
    WriteUint("", matDenF);
    WriteUint("", matSignDenF);
    WriteUint("", matNomF);
    WriteUint("", matSignNomF);
    WriteInt("", matCoefNomF);
    ullint ttni, ttpo;
    int lo = 1;
    for(int i=0; i<matDenF.size(); i++)
    {
        tex<<"\\frac{";
        for(int j=0; j<matNomF[i].size(); j++)
        {
            if(matCoefNomF[i][j]==-1)
                tex<<"-";
            else if(matCoefNomF[i][j]==1)
                tex<<"+";
            else if(matCoefNomF[i][j]<-1)
                tex<<matCoefNomF[i][j];
            else
                tex<<"+"<<matCoefNomF[i][j];
            ttni=matSignNomF[i][j];
            ttpo=matNomF[i][j]^ttni;
            lo = 1;
            while(ttni)
            {
                if(ttni&1)
                    tex<<"f_{"<<lo<<"}^{-}";
                ttni>>=1;
                lo++;
            }
            lo = 1;
            while(ttpo)
            {
                if(ttpo&1)
                    tex<<"f_{"<<lo<<"}^{+}";
                ttpo>>=1;
                lo++;
            }
        }
        tex<<"}{";
        for(int j=0; j<matDenF[i].size(); j++)
        {
            ttni=matSignDenF[i][j];
            ttpo=matDenF[i][j]^ttni;
            lo = 1;
            tex<<"(";
            while(ttni)
            {
                if(ttni&1)
                    tex<<"-E_{"<<lo<<"}";
                ttni>>=1;
                lo++;
            }
            lo = 1;
            while(ttpo)
            {
                if(ttpo&1)
                    tex<<"+E_{"<<lo<<"}";
                ttpo>>=1;
                lo++;
            }
            tex<<")";
        }
        tex<<"}";
        tex<<"\\\\";
        tex<<endl;
    }
}

bool evalCycle(ullint CY,const int n)
{
    int nEdg = 1, i = 1;
    for(i=1; i<=n; i++)
    {
        PairEdg[nEdg]=CY&Den0[i];
        if(PairEdg[nEdg])
        {
            NumC[nEdg] = i;
            nEdg++;
        }
    }

    if(countSetBits0(CY)==2)
        if((tp[0][NumC[1]]&CY && tp[1][NumC[1]]&CY) || (tp[2][NumC[1]]&CY && tp[3][NumC[1]]&CY))
        {
            CycNum[szS][1] = NumC[1];
            CycNum[szS][2] = NumC[1];
            szEdg[szS] = nEdg-1;
            MatFin[szS] = 2*L0[CycNum[szS][1]-1]-1;//Matrix of first edges
            return true;
        }
    int nEdgTest = 2;
    bool Vesited[n+1] = {false};
    int index = PairEdg[1];//Initialize to first
    Vesited[1] = true;
    CycNum[szS][1] = NumC[1];
    while(nEdg!=nEdgTest)
    {
        for(i = 1; i<nEdg; i++)
            if(!Vesited[i] && index&PairEdg[i])
            {
                index = PairEdg[i];
                Vesited[i] = true;
                CycNum[szS][nEdgTest] = NumC[i];
                nEdgTest++;
            }
    }
    CycNum[szS][nEdg] = NumC[1];
    szEdg[szS] = nEdg;
    int inf = 1;
    if(PosL0[CycNum[szS][1]] == CycNum[szS][2] && tp[2][CycNum[szS][1]]&CY)//2i-1
        inf = 2*CycNum[szS][1]-1;
    else if(PosR0[CycNum[szS][1]] == CycNum[szS][2] && tp[3][CycNum[szS][1]]&CY)//2i
        inf = 2*CycNum[szS][1];
    else if(L0[CycNum[szS][1]-1] == CycNum[szS][2] && tp[0][CycNum[szS][1]]&CY)//2L[i]-1
        inf = 2*L0[CycNum[szS][1]-1]-1;
    else if(R0[CycNum[szS][1]-1] == CycNum[szS][2] && tp[1][CycNum[szS][1]]&CY) //2R[i]
        inf = 2*R0[CycNum[szS][1]-1];
    MatFin[szS] = inf;//Matrix of first edges
    return true;
}

bool validCycle(ullint CY,const int n)
{
    int nEdg = 1, i = 1;
    for(i=1; i<=n; i++)
    {
        PairEdg[nEdg]=CY&Den0[i];
        if(PairEdg[nEdg])
        {
            if(countSetBits0(PairEdg[nEdg])>2)
                return false;
            nEdg++;
        }
    }
    int nEdgTest = 2;
    bool Vesited[dn] = {false};
    int index = PairEdg[1];//Initialize to first
    Vesited[1] = true;
    while(index)
    {
        for(i = 1; i<nEdg; i++)
            if(!Vesited[i] && index&PairEdg[i])
            {
                index^=PairEdg[i];
                Vesited[i] = true;
                nEdgTest++;
            }
    }

    return nEdgTest == nEdg;
}

void combining(int m, int t, int n)
{
    ullint CY = 0;
    int i = 1, j = 1;
    for(i = 1; i <= t; i++)
        c[i] = i ;
    c[t+1] = m+1;
    c[t+2] = 0;
    for(;;)
    {
        CY = 0;
        for(i = 1; i <= t; i++)
            CY^=F[c[i]];
        if(!(countSetBits0(CY)&1))//We choose only even cycles
            if(validCycle(CY,n))
            {
                if(evalCycle(CY,n))
                {
                    S[szS] = CY;
                    szS++;
                }

            }
        j = 1;
        while(c[j]+1 == c[j+1])
        {
            c[j] = j;
            j++;
        }
        if(j > t)
            return;
        c[j]++;
    }
}

void edgCoef()
{
    int ntst = 0, signCyc = 0, i = 1, j = 1, k = 0;
    bool ToTest = true;
    bool eqnL[MAX_2N] = {false};
    int LPQL[MAX_2N] = {0};
    while(ToTest)
    {
        ToTest = false;
        for(j = 1; j<szSr; j++)
        {
            signCyc = 0;
            k=0;
            bool eqn = false;
            if(szEdgR[j]==2)//This equiv pair cycle
            {
                if(L0[CycNumR[j][1]-1]!=R0[CycNumR[j][1]-1])
                    cout<<"PLEAZE ALERT REVIRIFER"<<endl;
                signCyc=LPQ[2*L0[CycNumR[j][1]-1]-1]-LPQ[2*R0[CycNumR[j][1]-1]];
                LPQL[k] = 2*L0[CycNumR[j][1]-1]-1;
                k++;
                LPQL[k] = 2*R0[CycNumR[j][1]-1];
                eqnL[LPQL[k]] = true;
                k++;
            }

            else
                for(i=1; i<szEdgR[j]; i++)
                {
                    if(PosL0[CycNumR[j][i]] == CycNumR[j][i+1] && tp[2][CycNumR[j][i]]&Sr[j])//2i-1
                    {
                        signCyc+=LPQ[2*CycNumR[j][i]-1];
                        LPQL[k] = 2*CycNumR[j][i]-1;
                        k++;
                    }

                    else if(PosR0[CycNumR[j][i]] == CycNumR[j][i+1] && tp[3][CycNumR[j][i]]&Sr[j])//2i
                    {
                        signCyc+=LPQ[2*CycNumR[j][i]];
                        LPQL[k] = 2*CycNumR[j][i];
                        k++;
                    }

                    else if(L0[CycNumR[j][i]-1] == CycNumR[j][i+1] && tp[0][CycNumR[j][i]]&Sr[j])//2L[i]-1
                    {
                        signCyc-=LPQ[2*L0[CycNumR[j][i]-1]-1];
                        LPQL[k] = 2*L0[CycNumR[j][i]-1]-1;
                        k++;
                    }
                    else if(R0[CycNumR[j][i]-1] == CycNumR[j][i+1] && tp[1][CycNumR[j][i]]&Sr[j]) //2R[i]
                    {
                        signCyc-=LPQ[2*R0[CycNumR[j][i]-1]];
                        LPQL[k] = 2*R0[CycNumR[j][i]-1];
                        k++;
                    }
                }
            if(signCyc == 0)
            {
                ToTest = true;
                LPQ[MatFinR[j]] += 2;//Increment the coefficient of the first edge by 2 to ensure odd cycle != 0
                break;//Repeat from beginning
            }
        }
        ntst++;
        if(ntst == 1000)
        {
            cout<<"this hug !"<<endl;
            break;
        }
    }
}

void buildEq()
{
    int signCyc = 0, i = 1, j = 1;
    short int tMatEq[2*MAX_N] = {0};
    for(j = 1; j<szS; j++)
    {
        signCyc = 0;
        for(i=1; i<=dn; i++)
            tMatEq[i] = 0;
        if(szEdg[j]==2)
        {
            signCyc = 0;
            tMatEq[2*L0[CycNum[j][1]-1]-1] = 1;
            tMatEq[2*R0[CycNum[j][1]-1]] = -1;
        }
        else
            for(i=1; i<szEdg[j]; i++)
            {

                if(PosL0[CycNum[j][i]] == CycNum[j][i+1] && tp[2][CycNum[j][i]]&S[j])//2i-1
                {
                    signCyc++;
                    tMatEq[2*CycNum[j][i]-1] = 1;
                }
                else if(PosR0[CycNum[j][i]] == CycNum[j][i+1] && tp[3][CycNum[j][i]]&S[j])//2i
                {
                    signCyc++;
                    tMatEq[2*CycNum[j][i]] = 1;
                }
                else if(L0[CycNum[j][i]-1] == CycNum[j][i+1] && tp[0][CycNum[j][i]]&S[j])//2L[i]-1
                {
                    signCyc--;
                    tMatEq[2*L0[CycNum[j][i]-1]-1] = -1;
                }
                else if(R0[CycNum[j][i]-1] == CycNum[j][i+1] && tp[1][CycNum[j][i]]&S[j]) //2R[i]
                {
                    signCyc--;
                    tMatEq[2*R0[CycNum[j][i]-1]] = -1;
                }
            }
        if(signCyc < szEdg[j]-1 && signCyc > -szEdg[j]+1)
        {
            Sr[szSr]=S[j];
            szEdgR[szSr]=szEdg[j];
            for(i=1; i<=szEdg[j]; i++)
                CycNumR[szSr][i]=CycNum[j][i];
            MatFinR[szSr] = MatFin[j];
            szSr++;
            for(i=1; i<=dn; i++)
                MatEq[nEq][i] = tMatEq[i];
            nEq++;
        }
    }
}

void genCycles(ullint tr, int n)
{
    ullint B = noneb&(~tr);//The complement of tree which represent the complement of graph from the tree G=B U tr
    B^=tde;//Delete HF circuits
    int  i = n, j = 0, l = 1, r = 1, nxt = 0,  v1, v2;
    for(i=n; i>=1; i--)
    {
        Den[i]=Den0[i];//Construct first denominators
        r = 1;
        if(tr&tp[0][i])
        {
            br[i][r] = L0[i-1];
            Posbr[i][br[i][r]]=r;
            r++;
        }
        if(tr&tp[1][i])
        {
            br[i][r] = R0[i-1];
            Posbr[i][br[i][r]]=r;
            r++;
        }
        if(tr&tp[2][i])
        {
            br[i][r] = PosL0[i];
            Posbr[i][br[i][r]]=r;
            r++;
        }
        if(tr&tp[3][i])
        {
            br[i][r] = PosR0[i];
            Posbr[i][br[i][r]]=r;
            r++;
        }
        nt[i] = r-1;
    }
    while(j<n-1)
    {
        for(r=n; r>=1; r--)
        {
            if(nt[r]==1)
            {
                nxt = br[r][1];
                Den[nxt]^=Den[r];
                v1 = r;
                v2 = br[nxt][nt[nxt]];
                swap(br[nxt][Posbr[nxt][r]],br[nxt][nt[nxt]]);
                swap(Posbr[nxt][v1],Posbr[nxt][v2]);
                nt[nxt]--;
                nt[r]--;
                DenF[l]=Den[r];
                l++;
                j++;
            }
        }
    }
    j = 1;
    while(B)
    {
        F[j] = B&~(B-1);
        B^=F[j];
        for(i=1; i<n; i++)
            if(F[j]&DenF[i])
                F[j]|=tr&DenF[i];
        if(!(countSetBits0(F[j])&1))//We choose only even cycles
            if(evalCycle(F[j],n))
            {
                S[szS] = F[j];
                szS++;
            }
        j++;
    }
    for(i=2; i<=j-1; i++)
        combining(j-1, i,n);
}

bool fraction(ullint tr, int n)
{
    int r = 1, r1 = 1;
    ullint B = noneb&(~tr),B0;//The complement of tree which represent the complement of graph from the tree G=B U tr
    B^=tde;//Delete HF circuits
    B0 = B;
    int nb = 1;
    int cfb[MAX_2N] = {0}, cfc[MAX_2N] = {0};
    while(nb<=dn)
    {
        if(B0&1)
            cfc[nb] = LPQ[nb];
        else
            cfb[nb] = LPQ[nb];
        nb++;
        B0>>=1;
    }
    for(int i=n; i>=1; i--)
    {
        Den[i]=Den0[i];//Construct first denominators
        Nig[i]=tp[0][i]|tp[1][i];//Construct first negative sign of denominators
        r = 1;
        r1 = 1;
        if(tr&tp[0][i])
        {
            br[i][r] = L0[i-1];
            Posbr[i][br[i][r]]=r;
            branches[i][L0[i-1]] = 2*L0[i-1]-1;
            oriArrBr[i][L0[i-1]] = true;
            r++;
        }
        else if(B&tp[0][i])
        {
            chords[i][r1] = 2*L0[i-1]-1;
            oriArrCh[i][r1] = true;
            r1++;

        }
        if(tr&tp[1][i])
        {
            br[i][r] = R0[i-1];
            Posbr[i][br[i][r]]=r;
            branches[i][R0[i-1]] = 2*R0[i-1];
            oriArrBr[i][R0[i-1]] = true;
            r++;
        }
        else if(B&tp[1][i])
        {
            chords[i][r1] = 2*R0[i-1];
            oriArrCh[i][r1] = true;
            r1++;
        }
        if(tr&tp[2][i])
        {
            br[i][r] = PosL0[i];
            Posbr[i][br[i][r]]=r;
            branches[i][PosL0[i]] = 2*i-1;
            oriArrBr[i][PosL0[i]] = false;
            r++;
        }
        else if(B&tp[2][i])
        {
            chords[i][r1] = 2*i-1;
            oriArrCh[i][r1] = false;
            r1++;
        }
        if(tr&tp[3][i])
        {
            br[i][r] = PosR0[i];
            Posbr[i][br[i][r]]=r;
            branches[i][PosR0[i]] = 2*i;
            oriArrBr[i][PosR0[i]] = false;
            r++;
        }
        else if(B&tp[3][i])
        {
            chords[i][r1] = 2*i;
            oriArrCh[i][r1] = false;
            r1++;
        }

        nt[i] = r-1;
        degVrtx[i] = r1-1;
    }
    int j = 0, nxt = 0, l = 1, v1, v2;
    while(j<n-1)
    {
        for(r=n; r>=1; r--)
        {
            if(nt[r]==1)
            {
                nxt = br[r][1];
                Den[nxt]^=Den[r];
                Nig[nxt]^=Nig[r];
                for(int i=1; i<=degVrtx[r]; i++)
                {
                    if(oriArrBr[r][nxt])//This indicate entered arrow
                    {
                        if(oriArrCh[r][i])//This indicate entered arrow
                            cfc[chords[r][i]]-=cfb[branches[r][nxt]];
                        else
                            cfc[chords[r][i]]+=cfb[branches[r][nxt]];
                        degVrtx[nxt]++;
                        oriArrCh[nxt][degVrtx[nxt]] = oriArrCh[r][i];
                        chords[nxt][degVrtx[nxt]] = chords[r][i];
                    }

                    else //This indicate sorted arrow
                    {
                        if(oriArrCh[r][i])//This indicate entered arrow
                            cfc[chords[r][i]]+=cfb[branches[r][nxt]];
                        else
                            cfc[chords[r][i]]-=cfb[branches[r][nxt]];
                        degVrtx[nxt]++;
                        oriArrCh[nxt][degVrtx[nxt]] = oriArrCh[r][i];
                        chords[nxt][degVrtx[nxt]] = chords[r][i];
                    }
                }
                v1 = r;
                v2 = br[nxt][nt[nxt]];
                swap(br[nxt][Posbr[nxt][r]],br[nxt][nt[nxt]]);
                swap(Posbr[nxt][v1],Posbr[nxt][v2]);
                nt[nxt]--;
                nt[r]--;
                Nig[r]=Nig[r]&Den[r];
                if(tr&Nig[r])
                    Nig[r]^=Den[r];
                DenF[l]=Den[r];
                NigF[l]=Nig[r];
                l++;
                j++;
            }
        }
    }
    ullint SignNom = 0, st;
    for(int k =1; k<=dn; k++)//Translate to binary
    {
        if(cfc[k]==0) continue;
        else if(cfc[k]>0)
        {
            st = pow(2,k-1);
            SignNom|=st;
        }
        if(cfb[k]==0 && cfc[k]==0)
            cout<<"ALERRTTTTTTTT !!!!!!!!!!!!"<<endl;
    }
    Sort(DenF, NigF, n);
    nDe++;
    vector<ullint> tmpD, tmpN, tmpNo, tmpSN;
    vector<int> tmpCN;
    for(int k=1; k<n; k++)
    {
        tmpD.push_back(DenF[k]);
        tmpN.push_back(NigF[k]);
    }
    tmpNo.push_back(B);
    tmpSN.push_back(SignNom);
    tmpCN.push_back(1);
    matDen.push_back(tmpD);
    matSignDen.push_back(tmpN);
    matNom.push_back(tmpNo);
    matSignNom.push_back(tmpSN);
    matCoefNom.push_back(tmpCN);
    return true;
}

bool decompression(ullint p, int n)
{
    if(p==n-1)
    {
        if(ATr==0)
        {
            genCycles(Ptt,n);
            buildEq();
            edgCoef();
        }
        fraction(Ptt,n);
        ATr++;
    }
    else
    {
        for(int i=0; i<sz[p]; i++)
        {
            Ptt|=Lb[p][i];
            decompression(p+1,n);
            Ptt^=Lb[p][i];
        }
    }
    return true;
}

bool spanTrees(ullint *tt,int k, int n)
{
    if(k==n-1)
    {
        for(int ii=0; ii<n-1; ii++)
            sz[ii]=countSetBits(tt[ii],ii);
        decompression(0,n);
    }
    else
    {
        for(int i=1; i<=n-k-1; i++)
        {
            if(edjTF[n-k][i]==0) continue;
            tt[k]=edjTF[n-k][i];
            for(int j=1; j<i; j++)
                edjTF[i][j]|=edjTF[n-k][j];
            spanTrees(tt,k+1,n);
            tt[k]=0;
            for(int j=1; j<i; j++)
                edjTF[i][j]^=edjTF[n-k][j];

        }
    }
    return true;
}

void initialiseLabel(int n)
{
    for(int i=1; i<=dn; i++)
        LPQ[i] = 1;//This for edge coefficient lists
    ATr = 0;
    Ptt = 0;
    szS = 1;
    szSr = 1;
    nEq = 1;
    nDe = 0;
    if(!matDen.empty())
    {
        matDen.clear();
        matSignDen.clear();
        matNom.clear();
        matSignNom.clear();
        matCoefNom.clear();
    }
    for(int i=1; i<=n; i++)
    {
        if(L0[i-1]==R0[i-1])
            LPQ[2*L0[i-1]-1] = 3;//The coefficient of equiv pair is 2

        PosL0[L0[i-1]]=i;
        PosR0[R0[i-1]]=i;
        nt[i] = 1;
        tt[i-1] = 0;
    }
    noneb = pow(2,2*n)-1;
    ullint tp1 = 0;
    bool notpr = false;
    int notpri = 0;
    for(int j=n; j>1; j--)
    {
        for(int i=n; i>=0; i--)
            edjTF[j][i] = 0;
        if(L0[j-1]<j)
        {
            tp1 = pow(2,2*L0[j-1]-2);
            edjTF[j][L0[j-1]] |= tp1;
        }
        if(R0[j-1]<j)
        {
            tp1=pow(2,2*R0[j-1]-1);
            edjTF[j][R0[j-1]] |= tp1;
        }
        if(PosL0[j]<j)
        {
            tp1 = pow(2,2*j-2);
            edjTF[j][PosL0[j]] |= tp1;
        }
        if(PosR0[j]<j)
        {
            tp1 = pow(2,2*j-1);
            edjTF[j][PosR0[j]] |= tp1;
        }
        notpri = 0;
        for(int ii=1; ii<j; ii++)
            if(edjTF[j][ii]==0)
            {
                notpri++;
                break;
            }
        if(notpri==j-1)
            notpr = true;
    }
    if(notpr)
        cout<<"Plz verifier LN = "<<LN<<endl;
    for(int i=n; i>=1; i--)
    {
        tp[0][i]=0;
        tp[1][i]=0;
        tp[2][i]=0;
        tp[3][i]=0;
        if(L0[i-1]!=i)
            tp[0][i] = pow(2,2*L0[i-1]-2);
        if(R0[i-1]!=i)
            tp[1][i] = pow(2,2*R0[i-1]-1);
        tp[2][i] = pow(2,2*i-2);
        tp[3][i] = pow(2,2*i-1);
        Den0[i]=tp[0][i]|tp[1][i]|tp[2][i]|tp[3][i];//Construct first denominators
        while(Den0[i]&tde)
            Den0[i]^=(Den0[i]&tde);
    }
spanTrees(tt,0,n);
}

void CycGen(const int n)
{
    ic[0]=1;
    jc[0]=n;
    ic[1]=ic[0];
    jc[1]=jc[0]-ic[0];
    NumCyEv(1);
    FIL[v][n]=1;
    v++;
    int r = 1;
    for(int q=0; q<v; q++)
    {
        r=1;
        for(int k=1; k<=n; k++)
        {
            lnc[q]+=FIL[q][k];
            if(FIL[q][k]!=0)
            {
                for(int l=1; l<=FIL[q][k]; l++)
                {
                    CFIL[q][r]=k;
                    Dsz[q][r] = 2*CFIL[q][r];
                    Hsz[q][r] = CFIL[q][r]/2;
                    Indx[q][r]=k;
                    Indx[q][r]+=Indx[q][r-1];
                    r++;
                }
            }
        }
    }
    return;
}

int Init(int q, const int n)
{
    for(int i=1; i<=n; i++)
    {
        L[i] = i;
        Lc[i] = i;
        Lc0[i] = i;
        PosL[i] = i;
        LisGenDet[i]=0;
        LisSizDet[i]=0;
        Matbeg[i]=0;
    }
    int r = 1, j = 1;
    for(int i=1; i<=n; i++)
    {
        if(FIL[q][i]!=0)
        {
            if(FIL[q][i]>1)
            {
                LisGenDet[r]=FIL[q][i];
                LisSizDet[r]=i;
                Matbeg[r]=j-1;
                r++;
            }
            j=j+FIL[q][i];
        }
    }
    return r-1;
}

void Distrib(int v, int eps, const int n)
{
    int szALLdet = 0;
    for(int q=0; q<v; q++)
    {
        szALLdet = Init(q,n);
        int sig = 1;
        if(eps == -1)
            for(int k=1; k<=lnc[q]; k++)
                sig=sig*eps;
        else
            sig = pow(-1,n);
        Itir(1,q,szALLdet, sig, n);
    }
    return;
}

bool Itir(int p, int q, int szALLde, int sig, const int n)
{
    int i, j, k, l, r = 0, r1 = 0, si = 1;
    int syym;
    uint v1, v2;
    bool irrY, hfN;
    bool hf, nfnd = true;
    int dn = 2*n;
    if(p==n+1)
    {
        for(k=1; k<=lnc[q]; k++)
        {
            R[Indx[q][k-1]+1]=L[Indx[q][k]];
            for(j=Indx[q][k-1]+2; j<=Indx[q][k]; j++)
                R[j]=L[j-1];
        }
        if(lnc[q] != 1)
        {
            bool visited[n+1] = {false};
            jdfs = 1;
            DFSUtil(1, visited,L,R);
        }
        if(jdfs-1 == n || lnc[q] == 1)/*if not disconnected diagrams*/
        {
            hf = false;
            for(k=1; k<=n; k++)
                if(R[k]==k||L[k]==k)
                {
                    hf = true;
                    break;
                }
            hfN = true;
            if(irrOnly == 0 && hf)
                hfN = false;
            if(hfN)
            {
                irrY = true;
                if(irrOnly == 0)
                    irrY = irreducible(L, R, n);
                if(irrY)/*if not reducible v1*/
                {
                    ADD(tpL,L,n);
                    ADD(tpPosL,PosL,n);
                    dv=1;
                    syy=false;
                    if(!Filtre(1, lnc[q], q, L, tpL, tpPosL, szALLde, n))/*if there is not another equivalent diagram*/
                    {
                        for(k=1; k<=n; k++)
                            PosR[R[k]]=k;
                        ADD(tpL,L,n);
                        ADD(tpPosL,PosL,n);
                        ADD(tpR,R,n);
                        ADD(tpPosR,PosR,n);
                        PropreLabel(tpL,tpR,tpPosL,tpPosR, n);
                        for(j=0; j<n; j++)
                        {
                            L0[j] = tpL[j+1];
                            R0[j] = tpR[j+1];
                        }
                        tde=0;//to Delete HF circuits
                        if(hf)
                        {
                            for(j=0; j<n; j++)
                            {
                                if(L0[j]==j+1) tde|=1<<(2*j);
                                if(R0[j]==j+1) tde|=1<<(2*j+1);
                            }
                        }
                        AddToFillLR(tpL,tpR,n);
                        myfile<<",";
                        syym = sig*(dv-1);
                        myfile<<syym<<",";
                        tex<<"\\[";
                        if(syym<0 && syym!=-1)
                            tex<<"-\\frac{1}{"<<-syym<<"}";
                        else if(syym>0 && syym!=1)
                            tex<<"+\\frac{1}{"<<syym<<"}";
                        else if (syym==-1)
                            tex<<"-";
                        else if (syym==+1)
                            tex<<"+";
                        for(k=1; k<=n; k++)
                        {
                            tex<<"\\{"<<2*k-1<<","<<2*k<<"|V|"<<2*tpL[k]-1<<","<<2*tpR[k]<<"\\}";
                        }
                        for(k = 1; k<=n; k++)
                        {
                            if(tpL[k]==k)
                                tex<<"f_{"<<2*tpL[k]-1<<"}^{-}";
                            if(tpR[k]==k)
                                tex<<"f_{"<<2*tpR[k]<<"}^{-}";
                        }
                        tex<<"\\left(";
                        initialiseLabel(n);
                        tex<<"\\begin{array}{rcl}";
                        organizeAndWrite(n);
                        tex<<"\\end{array}";
                        tex<<"\\right)";
                        tex<<"\\]";
                        LN++;
                    }
                }
            }
        }
    }
    else
    {
        for(i=p; i<=n; i++)
        {
            swap(L[i],L[p]);
            PosL[L[i]]=i;
            PosL[L[p]]=p;
            Itir(p+1, q, szALLde, sig, n);
            swap(L[i],L[p]);
        }
    }
    return true;
}

inline void ADD(uint *L1, uint *L2, int n)
{
    for(int k=1; k<=n; k++)
        L1[k]=L2[k];
}

int NumCyEv(int p)
{
    while(ic[p]<=jc[p])
    {
        for(int k=1; k<=p; k++)
            FIL[v][ic[k]]++;
        FIL[v][jc[p]]++;
        v++;
        ic[p+1]=ic[p];
        jc[p+1]=jc[p]-ic[p];
        NumCyEv(p+1);
        ic[p]++;
        jc[p]--;
    }
    return 0;
}

inline bool Equal(uint *L1,uint* L2, const int n)
{
    for(int i=1; i<=n; i++)
        if(L1[i]!=L2[i])
            return false;
    return true;
}

inline bool Mini(uint *L1, uint *L2, const int n)
{
    for(int i=1; i<=n; i++)
    {
        if(L1[i]==L2[i]) continue;
        if(L1[i]>L2[i])
            return true;
        else
            break;
    }
    return false;
}

bool Filtre(int k, int fin, int q,uint *L, uint *tpL, uint *tpPosL, int szALLde, const int n)
{
    bool adc;
    if(syy)
        return syy;
    if(k==fin+1)
    {
        if(szALLde!=0)
        {
            if(PermuteFiltre(q,1, L, tpL, tpPosL, szALLde, 1, n))
            {
                syy = true;
                return syy;
            }
        }
        else
        {
            if(Equal(L,tpL,n))
            {
                dv++;
            }
            if(Mini(L,tpL,n))
            {
                syy = true;
                return syy;
            }
        }
    }
    else
    {
        for(int ki=0; ki<Dsz[q][k]; ki++)
        {
            if(syy)
                break;
            if(ki==CFIL[q][k])
                REV(q, k, tpL, tpPosL);
            if(ki!=0)
                recswap(q, k, tpL, tpPosL);
            ADD(tpLk[k],tpL,n);
            ADD(tpPosLk[k],tpPosL,n);
            if(ki>=CFIL[q][k])
                FindR(q,k,tpL, tpPosL);
            Filtre(k+1, fin, q, L, tpL, tpPosL, szALLde, n);
            ADD(tpL,tpLk[k],n);
            ADD(tpPosL,tpPosLk[k],n);
        }
    }
    if(syy)
        return true;
    else
        return false;
}

bool PermuteFiltre(int q, int p, uint *L, uint *tpL,uint *tpPosL, int szALLde, int ld, const int n)
{
    bool adc;
    if(syy)
        return syy;
    if(p==LisGenDet[ld]+1)
    {
        ld++;
        if(ld==szALLde+1)
        {
            if(Equal(L,tpL,n))
            {
                dv++;
            }
            if(Mini(L,tpL,n))
            {
                syy = true;
                return syy;
            }
        }
        else
            PermuteFiltre(q, 1, L, tpL,tpPosL, szALLde, ld, n);
    }
    else
    {
        for(int i=p; i<=LisGenDet[ld]; i++)
        {
            if(syy)
                break;
            if(i!=p)
                for(int j=0; j<LisSizDet[ld]; j++)
                {
                    Swap(tpL, tpPosL, Indx[q][i+Matbeg[ld]-1]+1+j, Indx[q][p+Matbeg[ld]-1]+1+j);
                }
            PermuteFiltre(q,p+1, L,tpL, tpPosL, szALLde,ld, n);
            if(i!=p)
                for(int j=0; j<LisSizDet[ld]; j++)
                {
                    Swap(tpL, tpPosL, Indx[q][i+Matbeg[ld]-1]+1+j, Indx[q][p+Matbeg[ld]-1]+1+j);
                }

        }
    }
    if(syy)
        return true;
    else
        return false;
}

inline void recswap(int q, int k, uint *L, uint *PosL)
{
    Swap(L, PosL, Indx[q][k-1]+1, Indx[q][k]);
    for(int i=1; i<=CFIL[q][k]-2; i++)
    {
        Swap(L, PosL, Indx[q][k]-i+1, Indx[q][k]-i);
    }

    return;
}

inline void REV(int q, int k, uint *L, uint *PosL)
{
    for(int i=0; i<Hsz[q][k]; i++)
    {
        Swap(L,PosL, Indx[q][k-1]+1+i,Indx[q][k]-i);
    }

    return;
}

inline void FindR(int q, int k, uint *L, uint *PosL)
{
    swap(L[Indx[q][k-1]+1],L[Indx[q][k]]);
    PosL[L[Indx[q][k-1]+1]]=Indx[q][k-1]+1;
    PosL[L[Indx[q][k]]]=Indx[q][k];
    for(int i=1; i<=CFIL[q][k]-2; i++)
    {
        swap(L[i+Indx[q][k-1]],L[i+Indx[q][k-1]+1]);
        PosL[L[i+Indx[q][k-1]]]=i+Indx[q][k-1];
        PosL[L[i+Indx[q][k-1]+1]]=i+Indx[q][k-1]+1;
    }
    return;
}

inline void Swap(uint *L, uint *PosL, int v1, int v2)
{
    swap(L[v1],L[v2]);
    PosL[L[v1]]=v1;
    PosL[L[v2]]=v2;
    swap(L[PosL[v1]],L[PosL[v2]]);
    swap(PosL[v1],PosL[v2]);
    return;
}

bool irreducible(uint *L, uint *R, const int n)
{
    int indxL=1, indxR=1;
    bool VLR[n+1]= {false};
    bitset<MAX_2N> V[n+1]= {0};
    for(int i=1; i<=n; i++)
        V[i]=(1<<(1+2*(n-R[i])))+(1<<(2*n-2*L[i]))+(1<<(2*n-2*i))+(1<<(2*n+1-2*i));
    bitset<MAX_2N> S;
    for(int k=1; k<=n; k++)
    {
        indxL=k;
        indxR=k;
        for(int i=1; i<=n; i++)
            VLR[i] = false;
        S=V[k];
        VLR[k] = true;
        int j=1;
        while(true)
        {
            if(j==n-1)
                break;
            j++;
            indxR=R[indxR];

            if(!VLR[indxR])
                S=(S^V[indxR]);

            if(S.count()==2)
                return false;
            VLR[indxR]=true;
            indxL=L[indxL];
            if(!VLR[indxL])
                S=(S^V[indxL]);
            if(S.count()==2)
                return false;
            VLR[indxL]=true;
        }
    }
    return true;
}

void PropreLabel(uint *L, uint *R, uint *PosL, uint *PosR, const int n)
{
    uint v1,v2;
    bool visited[n+1] = {false};
    jdfs = 1;
    DFSUtil(1, visited,L,R);

    for(int i = 1; i<=n; i++)
        PosVrtxDFS[VrtxDFS[i]] = i;

    for(int i=1; i<=n; i++)
    {
        if(VrtxDFS[i]==i) continue;
        v1 = VrtxDFS[i];
        v2 = i;
        Swap(L,PosL,v1,v2);
        Swap(R,PosR,v1,v2);
        for(int j = 2; j<dvc; j++)
            Swap(MatS[j],PosMatS[j],v1,v2);
        swap(VrtxDFS[PosVrtxDFS[v1]],VrtxDFS[PosVrtxDFS[v2]]);
        swap(PosVrtxDFS[v1],PosVrtxDFS[v2]);
    }
    return;
}

int main()
{
    int n;
    irrOnly = 2;
    ostringstream stm ;
    cout << "Enter the order n" << endl;
    cin>>n;
    while(true)
    {
        cout<<"If you need to evaluate only irreducible diagrams enter the number 0"<<endl;
        cout<<"If you need to evaluate all diagrams (including HF) enter the number 1"<<endl;
        cin>>irrOnly;
        if(irrOnly == 0 || irrOnly == 1)
            break;
    }
    dn = 2*n;
    unsigned int maxD = ceil(pow(3.5,n-1));
    matDen.reserve(maxD), matSignDen.reserve(maxD), matNom.reserve(maxD), matSignNom.reserve(maxD), matCoefNom.reserve(maxD);
    posZero.resize(2*maxD), posOne.resize(2*maxD);
    bitOne.resize(2*maxD), bitZero.resize(2*maxD);
    CycGen(n);
    stm<<n;
    string sn = stm.str();
    string ss0="GrandPotential", ss1=".txt", sstx1=".tex";
    string ss=ss0+sn+ss1, sstx=ss0+sn+sstx1;
    myfile.open(ss);
    myfile<<"{";
    tex.open(sstx);
    tex<<"\\documentclass{article}"<<endl;
    tex<<"\\usepackage{geometry}"<<endl;
    tex<<"\\geometry{paperwidth=60cm,left=2cm,right=2cm,paperheight=29.7cm,top=1cm,height=26.5cm}"<<endl;
    tex<<"\\usepackage{amsmath}"<<endl;
    tex<<"\\begin{document}"<<endl;
    tex<<"The grand potential of the order "<<n<<endl;
    Distrib(v, -1, n);//-1 for fermions and +1 for bosons
    tex<<endl;
    tex<<"\\end{document}"<<endl;
    tex.close();
    myfile<<"Nothing}";
    myfile.close();
    return 0;
}
