package edu.utdallas.s3.vsa.main;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.List;
import java.util.zip.ZipException;

import org.json.JSONObject;
import org.json.JSONArray;

import soot.Scene;
import soot.options.Options;
import brut.androlib.AndrolibException;
import edu.utdallas.s3.vsa.base.GlobalStatistics;
import edu.utdallas.s3.vsa.graph.CallGraph;
import edu.utdallas.s3.vsa.graph.DGraph;
import edu.utdallas.s3.vsa.graph.IDGNode;
import edu.utdallas.s3.vsa.graph.ValuePoint;
import edu.utdallas.s3.vsa.utility.FileUtility;
import edu.utdallas.s3.vsa.utility.Logger;

public class Main_BLEUUID {

	static JSONObject config;
	static JSONObject targetMethds = new JSONObject();
	static Hashtable<String, String> m2m = new Hashtable<String, String>();

	static String pn;

	public static void startWatcher(int sec) {
		Thread t = new Thread() {
			public void run() {
				Logger.printE("I AM WATCHING U!");
				try {
					Thread.sleep(sec * 1000);
				} catch (InterruptedException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
				Logger.printE("TimeOut!TimeOut!TimeOut!TimeOut!");
				FileUtility.wf("./timeout.txt", pn, true);
				System.exit(0);
			}
		};
		t.setDaemon(true);
		t.start();
	}

	public static void main(String[] args) throws ZipException, IOException, AndrolibException {
		

		String apk = "";

		apk = args[0]; 

		System.out.println(apk);


		ApkContext apkcontext = ApkContext.getInstance(apk);
		Logger.TAG = apkcontext.getPackageName();
		pn = Logger.TAG;

		System.out.println(pn);

		soot.G.reset();
		Options.v().set_src_prec(Options.src_prec_apk);
		Options.v().set_process_dir(Collections.singletonList(apk));
		// Options.v().set_force_android_jar("./Android/Sdk/platforms/android-28/android.jar");
		Options.v().set_force_android_jar("android.jar");
		Options.v().set_process_multiple_dex(true);
		// Options.v().set_soot_classpath(ClassPath.get());
		Options.v().set_whole_program(true);
		Options.v().set_allow_phantom_refs(true);
		Options.v().set_output_format(Options.output_format_none);
		// Options.v().setPhaseOption("cg.spark", "on");
		// Options.v().setPhaseOption("cg.spark", "string-constants:true");
		Options.v().ignore_resolution_errors();

		long stime = System.currentTimeMillis();

		Scene.v().loadNecessaryClasses();
		startWatcher(60 * 8);

		CallGraph.init();

		String sig;
		List<Integer> regIndex;
		JSONObject result;


		HashMap<String, List<Integer>> targs = new HashMap<String, List<Integer>>();

		sig = "<android.bluetooth.le.ScanFilter$Builder: android.bluetooth.le.ScanFilter$Builder setServiceUuid(android.os.ParcelUuid)>";
		regIndex = Arrays.asList(0);
		targs.put(sig, regIndex);

		sig = "<android.bluetooth.le.ScanFilter$Builder: android.bluetooth.le.ScanFilter$Builder setServiceUuid(android.os.ParcelUuid,android.os.ParcelUuid)>";
		regIndex = Arrays.asList(0);
		targs.put(sig, regIndex);

		sig = "<android.bluetooth.le.ScanFilter$Builder: android.bluetooth.le.ScanFilter$Builder setServiceData(android.os.ParcelUuid,byte[])>";
		regIndex = Arrays.asList(0);
		targs.put(sig, regIndex);

		sig = "<android.bluetooth.le.ScanFilter$Builder: android.bluetooth.le.ScanFilter$Builder setServiceData(android.os.ParcelUuid,byte[],byte[])>";
		regIndex = Arrays.asList(0);
		targs.put(sig, regIndex);

		sig = "<android.bluetooth.BluetoothGatt: android.bluetooth.BluetoothGattService getService(java.util.UUID)>";
		regIndex = Arrays.asList(0);
		targs.put(sig, regIndex);

		// result = vs(targs);
		// result.put("alltime", System.currentTimeMillis() - stime);
		// FileUtility.wf("./res/" + pn, result.toString(), false);

		sig = "<android.bluetooth.BluetoothGattService: android.bluetooth.BluetoothGattCharacteristic getCharacteristic(java.util.UUID)>";
		regIndex = Arrays.asList(0);
		targs.put(sig, regIndex);

		sig = "<android.bluetooth.BluetoothGattCharacteristic: android.bluetooth.BluetoothGattDescriptor getDescriptor(java.util.UUID)>";
		regIndex = Arrays.asList(0);
		targs.put(sig, regIndex);

		result = vs(targs);
		result.put("alltime", System.currentTimeMillis() - stime);

		// FileUtility.wf("./res/" + pn, result.toString(), true);

		result = convertJS(result);
		FileUtility.wf("./res/" + pn, result.toString(), false);

	}

	public static JSONObject vs(HashMap<String, List<Integer>> targs) {
		long stime = System.currentTimeMillis();
		DGraph dg = new DGraph();

		List<ValuePoint> allvps = new ArrayList<ValuePoint>();
		List<ValuePoint> vps = null;
		JSONObject tmp;
		List<Integer> regIndex;

		for (String tsig : targs.keySet()) {
			regIndex = targs.get(tsig);
			System.out.println(tsig);
			vps = ValuePoint.find(dg, tsig, regIndex, 10000);
			for (ValuePoint vp : vps) {
				vp.print();
				// allvps.add(vp);

				if (!vp.getMethod_location().getDeclaringClass().toString().contains("no.nordicsemi")) {
					System.out.println("\n\n\n\nssss\n\n\n");
					allvps.add(vp);
				} else {
					dg.removeNode(vp);
				}

				// allvps.add(vp);
			}
			// allvps.addAll(vps);
		}

		dg.solve(allvps);

		JSONObject result = new JSONObject();

		for (IDGNode tn : dg.getNodes()) {
			Logger.print(tn.toString());
		}

		for (ValuePoint vp : allvps) {
			tmp = vp.toJson();
			if (tmp.has("ValueSet"))
				Logger.print(tmp.getJSONArray("ValueSet").toString());
			result.append("ValuePoints", tmp);
		}
		result.put("pname", pn);
		result.put("DGraph", dg.toJson());
		result.put("GlobalStatistics", GlobalStatistics.getInstance().toJson());

		long etime = System.currentTimeMillis();
		result.put("time", etime - stime);

		// FileUtility.wf("./res/" + pn, result.toString(), false);

		return result;
	}

	static String uuidreg = "[a-f0-9]{8}-[a-f0-9]{4}-[a-f0-9]{4}-[a-f0-9]{4}-[a-f0-9]{12}$";

	public static JSONObject convertJS(JSONObject result) {
		JSONObject fres = new JSONObject();
		fres.put("pkg", result.get("pname"));
		fres.put("uuids", new JSONObject());

		HashSet<String> uids = new HashSet<String>();
		if (result.has("ValuePoints")) {
			result.getJSONArray("ValuePoints").forEach((n) -> {
				uids.clear();

				JSONObject tvp = (JSONObject) n;
				if (tvp.has("ValueSet")) {
					tvp.getJSONArray("ValueSet").forEach((vs) -> {
						JSONObject tvs = (JSONObject) vs;
						if (tvs.has("0")) {
							tvs.getJSONArray("0").forEach((uuid) -> {
								String suuid = uuid + "";
								if (suuid.toLowerCase().matches(uuidreg))
									uids.add(suuid.toUpperCase());
							});
						}
					});
				}

				JSONObject uitem;
				for (String uuid : uids) {
					if (!fres.getJSONObject("uuids").has(uuid)) {
						uitem = new JSONObject();
						uitem.put("access", new JSONArray());
						uitem.put("define", new JSONArray());
						uitem.put("methods", new JSONArray());
						fres.getJSONObject("uuids").put(uuid, uitem);
					}
					uitem = fres.getJSONObject("uuids").getJSONObject(uuid);
					if (!jsContains(uitem.getJSONArray("define"), tvp.get("appendix")))
						uitem.append("define", tvp.get("appendix"));
					if (!jsContains(uitem.getJSONArray("methods"), tvp.get("SootMethod")))
						uitem.append("methods", tvp.get("SootMethod"));
				}

			});
		}

		return fres;
	}

	public static boolean jsContains(JSONArray ja, Object str) {
		for (Object obj : ja)
			if (str.equals(obj))
				return true;
		return false;
	}

	public static void wf(String content) {
		FileUtility.wf(Config.RESULTDIR + ApkContext.getInstance().getPackageName(), content, false);
	}

}
