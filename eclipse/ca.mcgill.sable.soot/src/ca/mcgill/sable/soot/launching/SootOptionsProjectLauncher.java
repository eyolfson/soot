/* Soot - a J*va Optimization Framework
 * Copyright (C) 2003 Jennifer Lhotak
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the
 * Free Software Foundation, Inc., 59 Temple Place - Suite 330,
 * Boston, MA 02111-1307, USA.
 */

package ca.mcgill.sable.soot.launching;

//import java.util.HashMap;

import java.util.ArrayList;

import org.eclipse.jface.action.*;
import org.eclipse.jface.dialogs.*;
//import ca.mcgill.sable.soot.SootPlugin;
import ca.mcgill.sable.soot.testing.*;
/**
 * @author jlhotak
 *
 * To change this generated comment edit the template variable "typecomment":
 * Window>Preferences>Java>Templates.
 * To enable and disable the creation of type comments go to
 * Window>Preferences>Java>Code Generation.
 */
public class SootOptionsProjectLauncher extends SootProjectLauncher {

	public void run(IAction action) {
		
		super.run(action);
		
		/*SootOptionsLauncherDialog dialog = new SootOptionsLauncherDialog(window.getShell(),
         getSootSelection().getProject());
      	dialog.open();
      	*/
      	/*TestDialog dialog = new TestDialog(window.getShell(),
         getSootSelection().getProject());
        dialog.open();
        
        IDialogSettings settings = SootPlugin.getDefault().getDialogSettings();
        System.out.println(settings.get("jimple_button_select")); 
        System.out.println(settings.get("jimp_button_select"));
        System.out.println(settings.get("grimp_button_select"));
        System.out.println(settings.get("b_button_select"));
        System.out.println(settings.get("baf_button_select"));
         */
      	/*if (dialog.getReturnCode() == Dialog.CANCEL) {	
      	}
      	else {
			IDialogSettings settings = SootPlugin.getDefault().getDialogSettings();
			String cmd = getCmd(settings.get("text_input"));
			runSootAsProcess(cmd);
			runFinish();
      	}*/
      	
      	/*OptionsDialog dialog = new OptionsDialog(window.getShell());
        dialog.open();
        if (dialog.getReturnCode() == Dialog.CANCEL) {	
      	}
      	else {
      		TestOptionsDialogHandler handler = new TestOptionsDialogHandler();
      		String cmd = getCmd(handler.getCmdLine());
			runSootAsProcess(cmd);
			runFinish();
      	}*/
      	PhaseOptionsDialog dialog = new PhaseOptionsDialog(window.getShell());
        setSdc(new SootDefaultCommands(dialog));
        presetDialog();
        dialog.open();
        if (dialog.getReturnCode() == Dialog.CANCEL) {	
        	SavedConfigManager scm = new SavedConfigManager();
			scm.setEditMap(dialog.getEditMap());
			scm.handleEdits();
      	}
      	else {
      		SootSavedConfiguration ssc = new SootSavedConfiguration("Temp", dialog.getConfig());
      		ssc.toSaveArray();
      		
      		
      		//HashMap temp = dialog.getOkMap();
      		//System.out.println("ok map: "+temp.get("test"));
      		//TestOptionsDialogHandler handler = new TestOptionsDialogHandler();
      		// TODO switch these 2 lines
      		
      		setCmd(ssc.toRunArray());
      		//setCmd(ssc.toRunString());
      		//System.out.println("to run soot main class "+dialog.getSootMainClass());
      		String mainClass = dialog.getSootMainClass();
      		//System.out.println("mainClass: "+mainClass);
      		if ((mainClass == null) || (mainClass.length() == 0)){
      			runSootDirectly();
      		}
      		else {
      			runSootDirectly(mainClass);
      		}
			runFinish();
			
			// save config if nessesary
			SavedConfigManager scm = new SavedConfigManager();
			scm.setEditMap(dialog.getEditMap());
			scm.handleEdits();
      	}
	}
	
	private void presetDialog() {
		//System.out.println("presetting dialog");
		getSdc().setOutputDir(getOutputLocation());
		//System.out.println("presetting output dir");
		getSdc().setSootClassPath(getSootClasspath().getSootClasspath()+getSootClasspath().getSeparator()+getProcess_path());
		//System.out.println("presetting cp");
		getSdc().setProcessPath(getProcess_path());
		//System.out.println("presetting process-path"+getProcess_path());
		getSdc().setKeepLineNum();
		//System.out.println("presetting keep line num");
		getSdc().setPrintTags();	
		//System.out.println("presetting print tags");
		getSdc().setSootMainClass();
	}
	
	// TODO use this method instaed of one with String
	private void setCmd(ArrayList user_cmd){
		getSootCommandList().addSingleOpt(user_cmd);
	}
	
	private void setCmd(String user_cmd) {
		
		
		//String output_path = LaunchCommands.OUTPUT_DIR+getOutputLocation();
		//getSootCommandList().addDoubleOpt(LaunchCommands.SOOT_CLASSPATH, getSootClasspath().getSootClasspath()+getSootClasspath().getSeparator()+getProcess_path());
		//StringBuffer classpath = new StringBuffer(LaunchCommands.SOOT_CLASSPATH);
		//classpath.append(getSootClasspath().getSootClasspath());
		//classpath.append(getSootClasspath().getSeparator());
 		//classpath.append(getProcess_path());
 	 		
		//StringBuffer cmd = new StringBuffer();
		//cmd.append(classpath+" ");
		getSootCommandList().addSingleOpt(user_cmd);
		//cmd.append(user_cmd+" ");
		//cmd.append(output_path+" ");
		//getSootCommandList().addDoubleOpt(LaunchCommands.PROCESS_PATH,getProcess_path());
		
	  	//return cmd.toString();
	}
}
