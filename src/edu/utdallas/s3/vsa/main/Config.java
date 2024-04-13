package edu.utdallas.s3.vsa.main;

public class Config {
	

	public static String RESULTDIR = "./valuesetResult/";
	public static String LOGDIR = "./logs/";

	public static String APPCONFIGDIR = "./../appsWithTargetHashes/";
	public static boolean PARSEINTERFACECALL = true;

	public static int MAXMETHODCHAINLEN = 100;
	
	public static int BackwardContextTimeOut = -1;

	static {
	}
}
