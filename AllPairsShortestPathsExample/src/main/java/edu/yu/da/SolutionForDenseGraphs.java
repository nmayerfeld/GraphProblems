package edu.yu.da;

import java.util.List;

public class SolutionForDenseGraphs extends WeAreAllConnectedBase{
    private double[][] distances;
    private WeAreAllConnectedBase.SegmentBase currentSolution;
    private int currentSolutionLowersBy=Integer.MIN_VALUE;
    private int n;
    public SolutionForDenseGraphs(){
        super();
    }
    @Override
    public WeAreAllConnectedBase.SegmentBase findBest(int n, List<SegmentBase> current, List<WeAreAllConnectedBase.SegmentBase> possibilities) {
        this.distances = new double[n][n];
        this.n = n;
        for(int i=0;i<n;i++){
            for(int j=0;j<n;j++){
                if(i==j) distances[i][j]=0;
                else distances[i][j]=Double.POSITIVE_INFINITY;
            }
        }
        System.out.println("after initialized with infinities, printing out distances");
        this.printDistances();
        for (WeAreAllConnectedBase.SegmentBase sb : current) {
            System.out.println("\nadding the following edge to graph");
            System.out.println("v1: "+sb.x+" v2: "+sb.y+" with length: "+sb.duration);
            System.out.println("changing distances["+sb.x+"]["+sb.y+"] from: "+distances[sb.x][sb.y]+" to "+sb.duration);
            distances[sb.x][sb.y] = sb.duration;
            System.out.println("changing distances["+sb.y+"]["+sb.x+"] from: "+distances[sb.y][sb.x]+" to "+sb.duration);
            distances[sb.y][sb.x] = sb.duration;
            this.printDistances();
        }
        System.out.println("\n\n after adding orig edges, printing");
        this.printDistances();
        this.preProcessDistances();
        for (WeAreAllConnectedBase.SegmentBase sb : possibilities) {
            this.checkPossibility(sb);
        }
        return this.currentSolution;
    }
    private void preProcessDistances(){
        System.out.println("\n\n preprocessing shortest distances");
        for(int k=0;k<n;k++){
            System.out.println("\n k = "+k);
            for(int i=0;i<n;i++){
                for(int j=0;j<n;j++){
                    if (distances[i][k]+distances[k][j]<distances[i][j])
                        distances[i][j]=distances[i][k]+distances[k][j];
                }
            }
            System.out.println("after calculating for k, shortest paths direct or stopping at 0->k is: ");
            this.printDistances();
        }
        this.printDistances();
    }
    private void printDistances(){
        System.out.println("printing distances");
        for(int i=0;i<n;i++){
            for(int j=0;j<n;j++){
                System.out.print(distances[i][j]+" ");
            }
            System.out.println();
        }
    }
    private void checkPossibility(WeAreAllConnectedBase.SegmentBase sb){
        int myTotalShortened=0;
        int[][]copy=new int[n][n];
        for(int i=0;i<n;i++){
            for(int j=0;j<n;j++){
                copy[i][j]= (int) distances[i][j];
            }
        }
        int v1=sb.x;
        int v2=sb.y;
        int length=sb.duration;
        for(int i=0;i<this.n;i++){
            for(int j=i;j<n;j++){
                double currentDistance=distances[i][j];
                if(distances[i][v1]+distances[v2][j]+length<currentDistance){
                    myTotalShortened+=currentDistance-(distances[i][v1]+distances[v2][j]+length);
                    currentDistance=distances[i][v1]+distances[v2][j]+length;
                    copy[i][j]= (int) (distances[i][v1]+distances[v2][j]+length);
                }
                if(distances[i][v2]+distances[v1][j]+length<currentDistance){
                    myTotalShortened+=currentDistance-(distances[i][v2]+distances[v1][j]+length);
                    copy[i][j]= (int) (distances[i][v2]+distances[v1][j]+length);
                }
            }
        }
        System.out.println("\n printing new copy after adding edge");
        for(int i=0;i<n;i++){
            for(int j=0;j<n;j++){
                System.out.print(copy[i][j]+" ");
            }
            System.out.println();
        }
        if(myTotalShortened>this.currentSolutionLowersBy){
            this.currentSolutionLowersBy=myTotalShortened;
            this.currentSolution=sb;
        }
        System.out.println("checked possibility from: "+sb.x+" to: "+sb.y+" with length: "+sb.duration);
        System.out.println("total shortened by was: "+myTotalShortened);
    }

}
