package edu.utdallas.s3.vsa.utility;

public class Logger {
	public static String TAG = "Logger";
	static boolean showMsg = false;

	public static void printI(String args) {
		if (showMsg)
			System.out.println(TAG + args);
	}

	public static void printW(String args) {
		String str = TAG + "[W]" + args;
		if (showMsg)
			System.out.println(str);
		FileUtility.wf("./logs/warnning.txt", str, true);
	}

	public static void print(String args) {
		if (showMsg)
			System.out.println(TAG + args);
	}

	public static void printE(String args) {
		args = TAG + args;
		// FileUtility.wf("./logs/error.txt", args, true);
		if (showMsg)
			System.out.println(args);
	}

}
