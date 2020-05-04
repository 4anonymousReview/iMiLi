package datag.handlers;
import datag.handlers.Rule;
import java.io.BufferedReader;
import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.FileOutputStream;
import java.io.FileWriter;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Locale;
import java.util.Map;
import java.util.Random;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.IPath;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IOpenable;
import org.eclipse.jdt.core.IPackageFragment;
import org.eclipse.jdt.core.IProblemRequestor;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.core.WorkingCopyOwner;
import org.eclipse.jdt.core.compiler.IProblem;
import org.eclipse.jdt.core.compiler.batch.BatchCompiler;
import org.eclipse.jdt.core.dom.AST;
import org.eclipse.jdt.core.dom.ASTParser;
import org.eclipse.jdt.core.dom.ASTVisitor;
import org.eclipse.jdt.core.dom.CompilationUnit;
import org.eclipse.jdt.core.dom.FieldDeclaration;
import org.eclipse.jdt.core.dom.MethodDeclaration;
import org.eclipse.jdt.core.dom.Modifier;
import org.eclipse.jdt.core.dom.Modifier.ModifierKeyword;
import org.eclipse.jdt.core.dom.Type;
import org.eclipse.jdt.core.dom.TypeDeclaration;
import org.eclipse.jdt.core.dom.VariableDeclarationFragment;
import org.eclipse.jdt.internal.compiler.Compiler;
import org.eclipse.jdt.internal.compiler.DefaultErrorHandlingPolicies;
import org.eclipse.jdt.internal.compiler.env.INameEnvironment;
import org.eclipse.jdt.internal.compiler.impl.CompilerOptions;
import org.eclipse.jdt.internal.compiler.problem.DefaultProblemFactory;
import org.eclipse.jdt.internal.compiler.ICompilerRequestor;
import org.eclipse.jdt.internal.compiler.IErrorHandlingPolicy;
import org.eclipse.jdt.internal.compiler.IProblemFactory;
import org.eclipse.jdt.internal.ui.text.correction.AssistContext;
import org.eclipse.jdt.internal.ui.text.correction.ProblemLocation;
import org.eclipse.jdt.internal.ui.text.correction.QuickFixProcessor;
import org.eclipse.jdt.ui.text.java.IInvocationContext;
import org.eclipse.jdt.ui.text.java.IJavaCompletionProposal;
import org.eclipse.jdt.ui.text.java.IProblemLocation;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.PlatformUI; 
import java.sql.*;
import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.IDocument;
//import javassist.compiler.Javac;
public class Generation {
	IProject project;
	IJavaProject javaProject;
	String[] key= {"abstract","assert","boolean","break","byte",
			"case","catch","char","class","const","continue","default",
			"do","double","else","enum","extends","final","finally","float",
			"for","goto","if","implements","import","instanceof","int","interface",
			"long","native","new","package","private","protected","public","return",
			"short","static","strictfp","super","switch","synchronized","this","throw",
			"throws","transient","try","void","volatile","while"};
	String [] type= {"int","float","long","String","char","boolean","double"};
	String[] token= {",",".","(",")","[","]","{","}",";","@","&&","||",
			"!","%","+","-","*","/","&","|","~","#"};
	String [] bio_token= {"{","}","[","]","(",")","\'","\"","/*","*/"};
	String []words=null;
	String word="";
	String []quotation_mark= {"//","/*","*/"};
	String [] bracket= {"{","}","(",")","[","]"};
	String Location4SeedProgram="D:\\projects";
	String Location4Mutants="D:\\Data1";
	int [] op_lo= {
			1,1,1,1,1,1,1,1,1,1,
			1,1,1,1,1,1,1,1,1,1,
			1,1,1,1,1,1,1,1,1,1,
			1,1,1,1,1,1
			};
	int count_op=op_lo.length;
	class Code 
	{
		String code;
		String mutant;
		int op;//operation_location number
		int p;//position
		String target;
		String object;
	};
	public Code mutate(Code C)
	{
		Random r=new Random();
		switch (C.op)
		{
		case 0://remove a keyword
			C.p=random_search_keyword(C.code);
			C.target=C.code.substring(C.p,search_wordtail(C.code,C.p));
			C.mutant=C.code.substring(0, C.p)+C.code.substring(search_wordtail(C.code,C.p));
			break;
		case 1://remove a character
			C.p=random_search_character(C.code);
			C.mutant=C.code.substring(0, C.p)+C.code.substring(C.p+1);
			C.target=C.code.substring(C.p,C.p+1);
			break;
		case 2://Replace a token with a character
			C.p=r.nextInt(C.code.length()-2);
			int l=r.nextInt(C.code.length()-1-C.p)+1;
			C.object=token[r.nextInt(token.length)];
			C.mutant=C.code.substring(0, C.p)+C.object+C.code.substring(C.p+l+1);
			C.target=C.code.substring(C.p,C.p+l+1);
			break;
		case 3://Replace a keyword with a token
			C.p=random_search_keyword(C.code);
			C.target=C.code.substring(C.p,search_wordtail(C.code,C.p));
			C.object=token[r.nextInt(token.length)];
			C.mutant=C.code.substring(0, C.p)+C.object+C.code.substring(search_wordtail(C.code,C.p));
			break;
		case 4://Remove an assignment
			C.p=search_character(C.code,"=");
			if(C.p<0)
				C.op=-1;
			else
			{
				C.target=C.code.substring(C.p,C.code.indexOf("\n", C.p));
				C.mutant=C.code.substring(0,C.p)+C.code.substring(C.p+C.target.length());
			}
			break;
		case 5://Remove a left/right bracket
			
			C.target=bracket[r.nextInt(bracket.length)];
			if(!C.code.contains(C.target))
			{
				C.op=-1;
				break;
			}
			else {
			C.p=search_character(C.code,C.target);
			if(C.p<0)
				C.op=-1;
			else
				C.mutant=C.code.substring(0, C.p)+C.code.substring(C.p+1);
			break;}
		case 6://Remove a quotation mark 
			int i6;
			C.target=quotation_mark[r.nextInt(quotation_mark.length)];
			if(!C.code.contains(C.target))
			{
				C.op=-1;
				break;
			}
			do {
				C.p=r.nextInt(C.code.length()/2);
						
			}while(!C.code.substring(C.p).contains(C.target));
			C.p=C.code.substring(C.p).indexOf(C.target);
			if(C.p+10>=C.code.length())
				C.mutant=C.code.substring(0, C.p);
			else
				C.mutant=C.code.substring(0, C.p)+C.code.substring(C.p+2);
			break;
		case 7://Replace a word with a character
			C.p=r.nextInt(C.code.length()-20);
			C.target=new Rule().search_word(C.code,C.p);
			C.object=token[r.nextInt(token.length)];
			C.p=C.code.indexOf(C.target, C.p);
			if(C.p>0)
			C.mutant=C.code.substring(0,C.p)+C.object+C.code.substring(search_wordtail(C.code,C.p));
			else
				C.op=-1;
			break;
		case 8://Delete a part of word
			int i8_1=r.nextInt(C.code.length()/2);
			while(!new Rule().word(C.code.toCharArray()[i8_1]))
				i8_1 ++;
			int i8_2=i8_1+1;
			while(new Rule().word(C.code.toCharArray()[i8_2]))
				i8_2 ++;
			int i8_3=r.nextInt(i8_2-i8_1);
			C.target=C.code.substring(i8_1,i8_1+i8_3);
			C.p=i8_1;
			C.mutant=C.code.substring(0,i8_1)+C.code.substring(i8_2);
			break;
		case 9://Change data types of variables
			
			C.target=type[r.nextInt(type.length)];
			C.object=type[r.nextInt(type.length)];
			C.p=search_character(C.code,C.target);
			if(C.p<0)
				C.op=-1;
			else
				C.mutant=C.code.substring(0, C.p)+C.object+C.code.substring(search_wordtail(C.code,C.p));
			break;
		case 10://Change visibility (’private’, ’protected’, and ’public’)
			String [] visibility= {"private","protected","public"};
			int l10;
			C.target=visibility[r.nextInt(visibility.length)];
			if(!C.code.contains(C.target))
			{
				C.op=-1;
				break;
			}
			do{
				l10=r.nextInt(C.code.length());
			}
			while(!C.code.substring(l10).contains(C.target));
			C.p=l10+C.code.substring(l10).indexOf(C.target);
			
			
			C.object=visibility[r.nextInt(visibility.length)];
			C.mutant=C.code.substring(0, C.p)+C.object+C.code.substring(search_wordtail(C.code,C.p));
			break;
		case 11:// Replace a keyword with another one. 
			C.p=random_search_keyword(C.code);
			C.target=C.code.substring(C.p,search_wordtail(C.code,C.p));
			C.object=key[r.nextInt(key.length)];
			C.mutant=C.code.substring(0, C.p)+C.object+C.code.substring(search_wordtail(C.code,C.p));
			break;
		case 12://Insert a token that starts with ’%’
			int a,b;
			a=r.nextInt(C.code.length()/2);
			b=r.nextInt(10);
			C.object="%"+C.code.substring(a, a+b);
			C.p=random_search_keyword(C.code);
			C.mutant=C.code.substring(0, C.p)+C.object+C.code.substring(C.p);
			break;
		case 13://try
			int l13;
			if(!C.code.contains("try"))
			{
				C.op=-1;
				break;
			}
			else 
			{
			do 
			{
				l13=r.nextInt(C.code.length());
				
			}while (!C.code.substring(l13).contains("try"));
			C.p=C.code.substring(l13).indexOf("try")+l13;
			} 
			C.target="try";
			C.mutant=C.code.substring(0, C.p)+C.code.substring(C.p+4);
			break;
		case 14://Insert a token that starts with ’%’
			int a1,b1;
			a1=r.nextInt(C.code.length()/2);
			b1=r.nextInt(10);
			C.object="%"+C.code.substring(a1, a1+b1);
			C.p=C.code.length()-1;
			C.mutant=C.code+C.object;
			break;
		case 15://Insert a token
			int a2,b2;
			a2=r.nextInt(C.code.length()/2);
			b2=r.nextInt(10);
			C.object=token[r.nextInt(token.length)]+C.code.substring(a2, a2+b2);
			C.p=random_search_keyword(C.code);
			C.mutant=C.code.substring(0, C.p)+C.object+C.code.substring(C.p);
			break;
		case 16://Insert a quotation mark
			C.object=quotation_mark[r.nextInt(quotation_mark.length)];
			C.p=r.nextInt(C.code.length());
			C.mutant=C.code.substring(0,C.p)+C.object+C.code.substring(C.p+1);
			break;
		case 17://Remove an import statement
			int l17;
			if(!C.code.contains("import"))
			{
				C.op=-1;
				break;
			}
			else 
			{
			do 
			{
				l17=r.nextInt(C.code.length());
				
			}while (!C.code.substring(l17).contains("import"));
			C.p=C.code.substring(l17).indexOf("import")+l17;
			} 
			C.target=C.code.substring(C.p,C.code.indexOf("\n", C.p));
			C.mutant=C.code.substring(0, C.p)+C.code.substring(C.code.indexOf("\n", C.p));
			break;
		case 18://Remove the words between two operators
			int l18;
			do {
				l18=r.nextInt(C.code.length()-1);
				
			}while(!token.toString().contains(C.code.substring(l18,l18+1)));
			int l18_1=l18+1;
			C.p=l18;
			while(l18_1<C.code.length()&&!token.toString().contains(C.code.substring(l18_1,l18_1+1)))
			{
				l18_1 ++;
			}
			if(l18_1==l18||l18_1>=C.code.length())
			{
				C.op=-1;
				break;
			}
			C.target=C.code.substring(l18,l18_1);
			C.mutant=C.code.substring(0,C.p)+C.code.substring(l18_1);
			break;
		case 19://Delete a token that ends or starts with '='\\
			int i19=r.nextInt(9);
			if(!C.code.contains("="))
			{
				C.op=-1;
				break;
			}
			else
			{
				do
				{
					C.p=r.nextInt(C.code.length()-10);
				}while(C.code.substring(C.p,C.p+i19).contains("="));
				C.target=C.code.substring(C.p,C.p+i19);
				C.mutant=C.code.substring(0,C.p)+C.code.substring(C.p+i19);
				break;
			}
		case 20://Delete a character
			int i20;
			do {
				i20=r.nextInt(C.code.length()-10);
			}while(new Rule().word(C.code.toCharArray()[i20]));
			C.p=i20;
			C.mutant=C.code.substring(0,C.p)+C.code.substring(C.p+1);
			C.target=C.code.substring(C.p,C.p+1);
			break;
		case 21://Delete the words between two opperators
			int i21_1;
			int i21_2;
			do {
				i21_1=r.nextInt(C.code.length()/2);
			}while(new Rule().word(C.code.toCharArray()[i21_1]));
			i21_2=i21_1+2;
			do {
				i21_2++;
			}while(new Rule().word(C.code.toCharArray()[i21_2]));
			C.target=C.code.substring(i21_1,i21_2);
			C.mutant=C.code.substring(0,i21_1)+C.code.substring(i21_2);
			break;
		case 22://Delete the data type
			for (int i22=0;i22<100;i22++)
			{
				C.p=r.nextInt(C.code.length()-10);
				C.target=type[r.nextInt(type.length)];
				if(C.code.substring(C.p).contains(C.target))
				{
					C.p=C.code.substring(C.p).indexOf(C.target);
					C.mutant=C.code.substring(0,C.p)+C.code.substring(C.p+C.target.length());
					break;
				}			
			}
			break;
		case 23://Insert a comma;
			C.object=",";
			C.p=0;
			C.mutant=C.object+C.code;
			break;
		case 24://Insert a comma;
			C.object=",";
			C.p=C.code.length()-1;
			C.mutant=C.code.substring(0,C.p)+C.object;
			break;
		case 25://Insert a comma
			C.object=",";
			C.p=C.code.substring(r.nextInt(C.code.length()/2)).indexOf("\n");
			C.mutant=C.code.substring(0,C.p)+C.object+C.code.substring(C.p);
			break;
		case 26://Insert a comma
			C.object=",";
			C.p=C.code.substring(r.nextInt(C.code.length()/2)).indexOf("\n");
			C.mutant=C.code.substring(0,C.p+1)+C.object+C.code.substring(C.p+1);
			break;
		case 27://Insert a character into a word
			C.object=token[r.nextInt(token.length)];
			do
			{
				C.p=r.nextInt(C.code.length()-10);
			}while(!new Rule().word(C.code.toCharArray()[C.p]));
			C.mutant=C.code.substring(0,C.p)+C.object+C.code.substring(C.p);
			break;
		case 28://Insert a  brace, bracket, or square bracket
			C.object=bracket[r.nextInt(bracket.length)];
			C.p=0;
			C.mutant=C.object+C.code;
			break;
		case 29://Insert a  brace, bracket, or square bracket
			C.object=bracket[r.nextInt(bracket.length)];
			C.p=C.code.length()-1;
			C.mutant=C.code.substring(0,C.p)+C.object;
			break;
		case 30:
			C.object=bracket[r.nextInt(bracket.length)];
			C.p=C.code.substring(r.nextInt(C.code.length()/2)).indexOf("\n");
			C.mutant=C.code.substring(0,C.p)+C.object+C.code.substring(C.p);
			break;
		case 31:
			C.object=bracket[r.nextInt(bracket.length)];
			C.p=C.code.substring(r.nextInt(C.code.length()/2)).indexOf("\n");
			C.mutant=C.code.substring(0,C.p+1)+C.object+C.code.substring(C.p+1);
			break;
		case 32://Insert a keyword
			C.object=key[r.nextInt(key.length)];
			C.p=0;
			C.mutant=C.object+C.code;
			break;
		case 33://Insert a keyword
			C.object=key[r.nextInt(key.length)];
			C.p=C.code.length()-1;
			C.mutant=C.code.substring(0,C.p)+C.object;
			break;
		case 34://Insert a keyword
			C.object=key[r.nextInt(key.length)];
			C.p=C.code.substring(r.nextInt(C.code.length()/2)).indexOf("\n");
			C.mutant=C.code.substring(0,C.p)+C.object+C.code.substring(C.p);
			break;
		case 35://Insert a keyword
			C.object=key[r.nextInt(key.length)];
			C.p=C.code.substring(r.nextInt(C.code.length()/2)).indexOf("\n");
			C.mutant=C.code.substring(0,C.p+1)+C.object+C.code.substring(C.p+1);
			break;
		case 36://Replace a character with another character
			C.object=token[r.nextInt(token.length)];
			do
			{
				C.p=r.nextInt(C.code.length()-10);
			}while(new Rule().word(C.code.toCharArray()[C.p]));
			C.target=C.code.substring(C.p,C.p+1);
			C.mutant=C.mutant=C.code.substring(0,C.p)+C.object+C.code.substring(C.p+1);
			break;
		}
		return C;
	}
	public int search_character(String code,String c)
	{
		Random r= new Random();
		int p=0;
		if(code.contains(c))
		{
			do
			p=r.nextInt(code.length()-20);
			while(!code.substring(p).contains(c));
			p=code.substring(p).indexOf(c);
		}
		else p=-1;
		return p;
	}
	ArrayList<Integer> num1=new ArrayList();
	ArrayList<Integer> num2=new ArrayList();
	float tot=0;
	float unpass=0;
	float tp=0;//真案例
	float fp=0;//假案例
	float JE_1=0;
	float JE_2=0;
	ArrayList<Double> weight=new ArrayList();
	public void count(int x)
	{
		if(x<50)fp++;
		else tp++;
		if(num1.size()<1)
		{
			num1.add(x);
			num2.add(1);
		}
		else
		{
			if(num1.contains(x))
			{
				num2.set(num1.indexOf(x), num2.get(num1.indexOf(x))+1);
			}
			else
			{
				num1.add(x);
				num2.add(1);
			}
		}
			
	}
	
	public boolean print_num()
	{
		if(num1.size()<1)
			return false;
		int i,j,p;
		int x,y;
		x=0;
		y=200;
		p=0;
		for(i=0;i<num1.size();i++)
		{
			y=200;
			for(j=0;j<num1.size();j++)
			{
				if(num1.get(j)<y&&num1.get(j)>x)
				{
					y=num1.get(j);
					p=num1.indexOf(y);
				}
			}
			System.out.print("["+num1.get(p)+":"+num2.get(p)+"]    ");
			x=y;
		}
		System.out.println();
//		System.out.println("未通过率："+unpass+"/"+tot+"="+unpass/tot);
//		System.out.println("T/F："+tp+"/"+fp+"="+tp/fp);
		return true;
	}
	public Generation(IProject project,IJavaProject javaProject) {
		this.project=project;
		this.javaProject=javaProject;
	}
	
	
	public String cleancode(String x)
	{
		int a=x.indexOf("/*");
		int b=x.indexOf("*/");
		while(a>0&&b>a)
		{
			x=x.substring(0, a-1)+x.substring(b+1, x.length()-1);
			a=x.indexOf("/*");
			b=x.indexOf("*/");
		}
		System.out.println("step1");
		int c=x.indexOf("//");	
		while(c>0)
		{
			int i=0;
			for(i=c;i<x.length();i++)
			{
				if(x.charAt(i)=='\n')
					break;
			}
			x=x.substring(0, c-1)+x.substring(i+1,x.length()-1);
			c=x.indexOf("//");
		}
		return x;
	}

	public String decode(String x)
	{
		System.out.println("ready!");
		x=cleancode(x);
		System.out.println("clean!!!");
		String y="";
		int i,j1,j2;
		i=j1=j2=0;
		for (i=0;i<x.length();i++)
		{
			if (x.charAt(i)=='{')
			{
				j1=j2=i;
				for(;j2<x.length();j2++)
				{
					if (x.charAt(j2)=='}')
						break;
				}
				if(j2-1>j1+1)
					y+=decode(x.substring(j1+1, j2-1))+"\n*********\n";
				i=j2;
			}
		}
		System.out.println();
		if(j2<x.length()-1)
			y+=x.substring(0,j1)+x.substring(j2,x.length()-1)+"\n*********\n";
		return y;
	}

	public int position_change(String x,String y)
	{
		int k=0;
		int kk=1;
		while (k<x.length()&&k<y.length())
		{
			if(x.charAt(k)!=y.charAt(k))
				return kk;
			else
				if(x.charAt(k)=='\n')
					kk++;
			k++;
		}
		return -1;
	}
	class CH
	{
		String code;
		int c1;//变异
		String c2;//被操作
		String c3;//操作
		int c4;//操作符
		int p;//位置
		String[] name;
	};
	public void gener()
	{
		while(true)
		{
		float mu_total=0;
		float ec_true=0;
		float ec_false=0;
		float ec_tp=0;
		float ec_fp=0;
		float ec_equ=0;
		float ec_pass=0;
		float diff=0;
		float diff_1=0;
		float diff_2=0;
		System.out.println("AAAAAAAAAAAAAAAAAAA");
		try {
			Class.forName("com.mysql.cj.jdbc.Driver");	
			Connection conn = DriverManager.getConnection(
	                "jdbc:mysql://localhost:3306/wmy?serverTimezone=GMT&useSSL=false&useUnicode=true&amp",
	                "root","123456");
			String sql="insert into data values (?,?,?,?,?,?,?,?,?,?,?,?)";
			String sql_diff="insert into diff values (?,?,?,?,?,?,?,?,?,?,?,?,?)";
			String sql1="insert into diff1 values (?,?,?,?,?,?,?,?,?,?,?,?,?)";
			String sql2="insert into diff2 values (?,?,?,?,?,?,?,?,?,?,?,?,?)";
			if(conn.isClosed()) {System.out.println("未连接数据库");}
			else System.out.println(conn);
			PreparedStatement ps=conn.prepareStatement(sql);
			AST ast=AST.newAST(AST.JLS9);
			int Total=0;
			String[] name= {};
			String name1="";
			for(IPackageFragment pf:javaProject.getPackageFragments()) {
				for(ICompilationUnit icu:pf.getCompilationUnits()) {
					CompilationUnit cu=createCompilationUnit(icu);
					
					name1+=","+cu.getJavaElement().getElementName().substring(0,cu.getJavaElement().getElementName().length()-6 );
//					System.out.println(name1);	
				}
			}
			name=name1.substring(1,name1.length()).split(",");
			long start=System.currentTimeMillis(),end;
			int count=0;
			for(IPackageFragment pf:javaProject.getPackageFragments()) {
				for(ICompilationUnit icu:pf.getCompilationUnits()) {
					start =System.currentTimeMillis();
					CompilationUnit cu=createCompilationUnit(icu);
					System.out.println(cu.getJavaElement().getElementName()+"  ------  Begin");			
					String path=Location4Mutants+icu.getElementName();	
					File code=new File(path);
					code.createNewFile();
					String libs=getClasspath(Location4SeedProgram+project.getFullPath().toOSString()+"\\lib");
					path+=" -classpath \""+libs+Location4SeedProgram+project.getFullPath().toString()+"/src/\"";
					String res=compileCode(cu.toString(),path);
					
					if(calLineNum(res)!=-1) {System.out.println(icu.getElementName()+"有错误");continue;}
					
					Random r=new Random();
					String rw=return_words(cu.toString());
					word+=rw;
					words=word.substring(0,word.length()).split(",");//词表
					int T=200;//变异数量
					
					while(T-->0) {
						int count_i=0;
						for(int op_i=0;op_i<op_lo.length;op_i++)
							count_i +=op_lo[op_i];
						if(count_i!=count_op)
						{
							count_op=count_i;
							System.out.print("Delete Operator_Location Pair No.：");
							for(int op_i=0;op_i<op_lo.length;op_i++)
							{
								if(op_lo[op_i]<1)
								System.out.print(op_i+",");
							}
							System.out.println();
						}
						if(count_op==0)
						{
							System.out.println("No operator exists!");
							 System.exit(0);
							break;
						}
						tot++;
						mu_total++;
//						System.out.print('.');
						if(T%100==0)
						{
							System.out.println("----");
//							System.out.println("总数："+mu_total+"  通过："+ec_true+"  未通过："+ec_false+"  正例："+ec_tp+"  负例："+ec_fp);
							System.out.println("Total mutants："+mu_total+"  Each different:"+(mu_total-JE_1)+" "+((mu_total-JE_1)/mu_total)+"  At least one location different:"+(mu_total-JE_2)+" "+((mu_total-JE_2)/mu_total));
//							System.out.println("比例："+ec_true+"\\"+mu_total+"="+ec_true/mu_total);
							System.out.println("Total true bug mutants："+diff+"  Each different:"+(diff-diff_1)+" "+((diff-diff_1)/diff)+"  At least one location different:"+(diff-diff_2)+" "+((diff-diff_2)/diff));
							print_num();
						}
						if(T%100==0)
						{
							end=System.currentTimeMillis();
							System.out.println("Time for producing and testing 100 items ："+(end-start)/1000);
							start=System.currentTimeMillis();
							System.out.println("Total mutants：" +mu_total+"    Pass:"+ec_pass+"   Direct show mutated line:"+ec_equ);
						}

						String source="";
						String mod="";
						int flag=r.nextInt(7);
						int flag_p=r.nextInt(9);
//						class CH
//						{
//							String code;
//							int c1;//变异
//							String c2;//被操作
//							String c3;//操作
//							int c4;//操作符
//							int p;//位置
//							String[] name;
//						};
						Code c =new Code();
//						flag=r.nextInt(12);
						c.code=cu.toString();
						c.mutant=c.code;
						do
						{
							c.op=r.nextInt(36);
						}
						while(op_lo[c.op]==0||mutate(c).op<0);
						c.target=" ";
						c.object=" ";
						c.p=0;
						c=mutate(c);
//						int flag=5;//对应修改
						CH C=new CH();
						C.code=c.mutant;
						C.c1=c.op;
						C.c2=c.target;
						C.c3=c.object;
						C.c4=c.op;
						C.p=c.p;
						C.name=null;
						
						source=c.mutant;
						FileWriter fw=new FileWriter(code);
						fw.write(source);
						fw.close();
						
						libs=getClasspath(Location4SeedProgram+project.getFullPath().toOSString()+"\\lib");
						path=Location4Mutants+icu.getElementName();
						path+=" -classpath \""+libs+Location4SeedProgram+project.getFullPath().toString()+"/src/\"";
						res=compileCode(cu.toString(),path);
						String res2=javaccode("",path);
//						mu_total++;
						if(res.length()==0)
							ec_true++;
//						else
//							ec_false++;
						if(res.length()!=0) {
							
							int ln=calLineNum(res);
							if(ln==-1) {ec_pass++;continue;}
							int position=1;
							boolean yes=false;
//							System.out.println(res2);
							
							for(int i=0;i<Math.min(cu.toString().length(), source.length());i++) {
								if(cu.toString().charAt(i)!=source.charAt(i)) {
									yes=true;
									break;
								}
								if(source.charAt(i)=='\n') position++;
							}
							if(!yes) continue;
							int flag1=new Rule().situation(cu.toString(),C,res,res,position);
							if(flag1>50)
							{
								count++;
								if(count%100==99)
								{
									end=System.currentTimeMillis();
									System.out.println("耗时："+(start-end)/1000);
									start=System.currentTimeMillis();
								}
							}
							if(new Rule().rule_0(res, res, position)==1)
								ec_equ++;

							if(flag1<=0) continue;
							
							unpass++;
							count(flag1);
							if(flag1<50)
								ec_fp++;
							else
								ec_tp++;
							
							int flag_print=0;
							if(position==1)continue;
							if(flag1>50||flag1<=0)
							{
								System.out.println("XXXXXXXXXXXXXXXXXXXXXXXXXXX");
								
								ps.setString(1, cu.getJavaElement().getJavaProject().getElementName());//project
								ps.setString(2, cu.getPackage().getName().toString());//package
								ps.setString(3, cu.getJavaElement().getElementName());//class
								ps.setString(4, cu.toString());//ori
								ps.setString(5, source);//mod
								ps.setInt(6, position);//position
								ps.setString(7, new Rule().search_line1(res).toString());//报告位置
								ps.setString(8,res);
							//	ps.setString(9, res);
							//	ps.setString(10, new Rule().search_line2(res).toString());
								ps.setInt(9,C.c1);//操作
								ps.setString(10,C.c2);//被操作
								ps.setString(11,C.c3);//操作体
								ps.setInt(12, flag1);
								ps.execute();
								Total++;
								if(c.op>0)
									op_lo[c.op]=0;
							}		
							if(flag1>50)
							{
								System.out.println("Ture (print 1) or False:(print 2):");
								flag_print=(int) System.in.read(); 
								System.out.println("OK");	
							}
							if(flag_print==1)flag1=100;
							if(flag_print==2)flag1=0;
							int diff_flag=new Rule().situation(cu.toString(),C,res,res,position);
							if(diff_flag>50)
							{
								diff++;
								ps=conn.prepareStatement(sql_diff);
								if(new Rule().compare_line2(new Rule().search_line1(res),new Rule().search_line2(res2)))//至少一项一致
								{								
									diff_2++;
									
									
								}
								else
								{
									ps=conn.prepareStatement(sql2);
								}
								if(new Rule().compare_line(new Rule().search_line1(res),new Rule().search_line2(res2)))//至少一项一致
								{
									diff_1++;
									
									
								}
								else
								{
									ps=conn.prepareStatement(sql1);
								}
								ps.setString(1, cu.getJavaElement().getJavaProject().getElementName());//project
								ps.setString(2, cu.getPackage().getName().toString());//package
								ps.setString(3, cu.getJavaElement().getElementName());//class
								ps.setString(4, cu.toString());//ori
								ps.setString(5, source);//mod
								ps.setInt(6, position);//position
								ps.setString(7, new Rule().search_line1(res).toString());//报告位置
								ps.setString(8,res);
							//	ps.setString(9, res);
							//	ps.setString(10, new Rule().search_line2(res).toString());
								ps.setInt(9,C.c1);//操作
								ps.setString(10,C.c2);//被操作
								ps.setString(11,C.c3);//操作体
								ps.setInt(12, flag1);
								ps.setString(13, res2);
								ps.execute();
								ps=conn.prepareStatement(sql);
							}
							if(new Rule().compare_line2(new Rule().search_line1(res),new Rule().search_line2(res2)))//至少一项一致
							{
								
								JE_2++;
								
							}
							if(new Rule().compare_line(new Rule().search_line1(res),new Rule().search_line2(res2)))//至少一项一致
							{
								JE_1++;
								
							}
							
					}

					}		
//					code.delete();
					
				}
			}
			System.out.println(Total);
			ps.close();			
			conn.close();
		}catch(Exception e) {
			e.printStackTrace();
		}		
	}
}	
	protected CompilationUnit createCompilationUnit(ICompilationUnit compilationUnit) {
		ASTParser parser = ASTParser.newParser(AST.JLS9);
		parser.setSource(compilationUnit);
		parser.setProject(compilationUnit.getJavaProject());
		IPath path=compilationUnit.getPath();
		parser.setUnitName(path.toString());
		parser.setResolveBindings(true);
		parser.setStatementsRecovery(true);
		CompilationUnit unit=null;
		try
		{
			unit= (CompilationUnit) parser.createAST(null);
		}catch(Exception e)
		{
			e.printStackTrace();
		}
		return unit;
	}
	private String javaccode(String code, String path) {
		try {
			Process process = Runtime.getRuntime().exec("javac "+path);
            InputStream inputStream = process.getErrorStream();
            InputStreamReader inputStreamReader = new InputStreamReader(inputStream, "GBK");
            BufferedReader bufferedReader = new BufferedReader(inputStreamReader);
            String line = null,res="";
            while ((line = bufferedReader.readLine()) != null) {
                res+=line+"\r\n";
            }
            
            return res;
		}catch(Exception e) {
			e.printStackTrace();
		}
		return "";
//		return eout.toString();
	}
	private String compileCode(String code,String path) {
//		System.out.println("===================="+path);
		OutputStream out = new ByteArrayOutputStream();
		PrintWriter pw= new PrintWriter(out,true);
		
		OutputStream eout = new ByteArrayOutputStream();
		PrintWriter epw= new PrintWriter(eout,true);
		BatchCompiler.compile(path, pw, epw, null);
		return eout.toString();
	}
	
	private String code_insert(String code,int r1,int r2,int r3) {

		switch(r2)
		{
		case 0:
			return code.substring(0, r1)+key[r3]+code.substring(r1, code.length());
		case 1:
			return code.substring(0, r1)+token[r3]+code.substring(r1, code.length());
		case 2:
			return code.substring(0, r1)+words[r3]+code.substring(r1, code.length());
		}
		return code;
	}


	
	public String code_line(String code)//随机一行
	{
		Random r=new Random();
		int j;
		String x;
		j=r.nextInt(code.length());
//		System.out.println("位置："+j);
		j=new Rule().p2line(code, j);
//		System.out.println("行"+j);
		x=new Rule().search_String(code, j);
		return x;
	}
	public String mix(String code)
	{
		String x="";
		Random r=new Random();
		int i=r.nextInt(5);
		int flag=0;
		int j;
		for (;i>=0;i--)
		{
			flag=r.nextInt(4);
//			System.out.println("flag:"+flag);
			switch (flag)
			{
			case 0:
				j=r.nextInt(key.length);
				x+=key[j];
				break;
			case 1:
				j=r.nextInt(token.length);
				x+=token[j];
				break;

			case 2:
				j=r.nextInt(code.length()-10);
				x+=code.substring(j,j+r.nextInt(10)).replace('\n', ' ');
				break;
			case 3:
				j=r.nextInt(words.length);
				x+=words[j];
				break;
			}
			
		}
		return x;
	}
	public String code_change4(String code, int r1,int r2)//替换
	{
		String x= new Rule().search_word(code,r1);
		int r;
		if(r1<x.length())r=0;
		else r=r1-x.length();
		int p=code.indexOf(x, r);
		if(p<0)
			p=code.indexOf(x);
		String x2=code.substring(0,p)+new Rule().search_word(code,r2)+code.substring(p+x.length());
		return x2;
	}
	public String code_change3_1(String code,int r1)
	{
		if(!new Rule().word(code.toCharArray()[r1]))
		{
			if(r1>code.length()-20)
			{
				while(!new Rule().word(code.toCharArray()[r1])&&r1>0)
					r1--;
			}
			else
			{
				while(!new Rule().word(code.toCharArray()[r1])&&r1<code.length()-1)
					r1++;
			}
				
		}
		int i1=r1;
		int i2=r1+1;
		if (i2>=code.length())i2=code.length()-1;
		while(i1>=0&&new Rule().word(code.toCharArray()[i1]))
			i1--;
		while(new Rule().word(code.toCharArray()[i2])&&i2<code.length()-1)
			i2++;
		if (i2>code.length()-1)i2=code.length()-1;
		if (i1<-1)i1=-1;
		if(i2<i1+1)i1=i2-1;
		return code.substring(i1+1,i2);
	}

	public String code_change3(String code,int r1)//删除一个词
	{
		
		if(!new Rule().word(code.toCharArray()[r1]))
		{
			if(r1>code.length()-20)
			{
				while(!new Rule().word(code.toCharArray()[r1])&&r1>0)
					r1--;
			}
			else
			{
				while(!new Rule().word(code.toCharArray()[r1])&&r1<code.length()-1)
					r1++;
			}
				
		}
		int i1=r1;
		int i2=r1+1;
		if (i2>=code.length())i2=code.length()-1;
		while(i1>0&&new Rule().word(code.toCharArray()[i1]))
			i1--;
		while(new Rule().word(code.toCharArray()[i2])&&i2<code.length()-1)
			i2++;
		return code.substring(0, i1)+code.substring(i2);
		
	}

	public String code_change1_1(String code,int r1)//删除空格
	{
		int i1=code.indexOf(" ", r1);
		int i2=code.indexOf(" ", i1+1);
		if(i2<=i1||i1<0)
		{
			i2=code.lastIndexOf(" ");
			i1=code.lastIndexOf(code, i2-1);
		}
		
		String x=code.substring(i1,i2);
		return x;
	}
	public String code_change1(String code,int r1)
	{
		int i1=code.indexOf(" ", r1);
		int i2=code.indexOf(" ", i1+1);
		if(i2<=i1||i1<0)
		{
			i2=code.lastIndexOf(" ");
			i1=code.lastIndexOf(code, i2-1);
		}
		String x=code.substring(0,i1)+code.substring(i2);
		return x;
	}
	public String code_change2_1(String code,int r1)
	{
		String x="";
		x=new Rule().search_String(code,new Rule().p2line(code, r1));
		return x;
	}
	public String code_change2(String code,int r1)//删除一行
	{
		String x="";
		x=new Rule().search_String(code,new Rule().p2line(code, r1));
		String x2="";
		x2=code.substring(0,code.indexOf(x))+code.substring(code.indexOf(x)+x.length());
		return x2;
	}
	public boolean contain_key(String code)
	{
		for(int i=0;i<key.length;i++)
		{
			if(code.contains(key[i]))
			{
				String x=code.replaceAll(key[i], "");
				for(int j=0;j<x.length();j++)
				{
					if(new Rule().word(x.toCharArray()[j]))
						return false;
				}
				return true;
			}
		}
		return false;
	}
	public int posi(String code,int situation)
	{
		Random r=new Random();
		int x= r.nextInt(code.length());
		int flag;
		String x2;
		switch(situation) {
		case 0://关键词定位
			flag=10000;
			
			while(flag>0)
			{
				x2=new Rule().search_word(code, x);
				if(contain_key(x2))
					return x;
				else x= r.nextInt(code.length());
				flag--;
			}
			break;
		case 1://非关键词定位
			flag=10000;
			while(flag>0)
			{
				if(!contain_key(new Rule().search_word(code, x)))
					return x;
				else x= r.nextInt(code.length());
				flag--;
			}
			break;
		case 2://临近符号
			flag=10000;
			while(flag>0)
			{
				x2=new Rule().search_word(code, x);
				if(contain_key(x2))
					break;
				else x= r.nextInt(code.length());
				flag--;
			}
			boolean flag2=r.nextBoolean();
			while(new Rule().word(code.toCharArray()[x])&&x>0&&x<code.length()-1)
			{
				if(flag2)
					x++;
				else x--;
			}
			
			return x;
		case 3:
			return r.nextInt(code.length());

		case 4:
			return num(code);
		case 5://孤独符号位
			return seek_token(code);
		case 6://多元符号位
			return seek_multitoken(code);
		case 7://成对匹配符号
			return seek_biotoken(code);
		case 8://行的首尾
			return seek_l(code);
		}
		return 0;
		
	}
	public int seek_l(String code)
	{
		int flag =100;
		Random r=new Random();
		int i=0;
		int j;
		while(flag>0)
		{
			j=r.nextInt(code.length());
			
			i=code.indexOf("\n", j);
			if(i>0)
				return i;
		}
		return (code.indexOf("\n"));
		
		
	}
	public int seek_biotoken(String code)
	{
		int flag=1000;
		int i=0;
		int i1,i2;
		while(flag>0)
		{
			i=seek_token(code);
			if (i<=0)i1=0;
			else i1=i-1;
			if(i>=code.length()-1)i2=code.length();
			else i2=i+1;
			for(int j=0;j<bio_token.length;j++)
			{
				if(code.substring(i1,i2).contains(bio_token[j]))
					return i;
			}
			flag--;
		}
		return -1;
	}
	
	public int seek_multitoken(String code)
	{
		Random r=new Random();
		int p=r.nextInt(code.length());
		boolean f=r.nextBoolean();
		while(p>=0&&p<code.length()-1)
		{
			if(!new Rule().word(code.toCharArray()[p])&&!new Rule().word(code.toCharArray()[p+1]))
				return p;
			if(f)p++;
			else p--;
		}
		p=0;
		while(p<code.length())
		{
			if(!new Rule().word(code.toCharArray()[p])&&!new Rule().word(code.toCharArray()[p+1]))
				return p;
			p++;
		}
		return seek_token(code);
	}
	public int seek_token(String code)
	{
		Random r=new Random();
		int p=r.nextInt(code.length());
		boolean f=r.nextBoolean();
		while(p>=0&&p<code.length())
		{
			if(!new Rule().word(code.toCharArray()[p]))
				return p;
			if(f)p++;
			else p--;
		}
		p=0;
		while(p<code.length())
		{
			if(!new Rule().word(code.toCharArray()[p]))
				return p;
			p++;
		}
		return -1;
	}
	public String return_words(String code)
	{
		String x="";
		int i,i1,i2;
		for (i=0;i<code.length();i++)
		{
			i1=i;
			while(new Rule().word(code.toCharArray()[i])&&i<code.length())
			{
				i++;
			}
			i2=i;
			if(!word.contains(code.substring(i1,i2))&&!x.contains(code.substring(i1,i2)))
				x+=','+code.substring(i1,i2);
		}
		return x;
	}
	public int num(String code)
	{
		Random r=new Random();
		int p=r.nextInt(code.length());
		boolean f=r.nextBoolean();
		while(p>=0&&p<code.length())
		{
			if(code.toCharArray()[p]>='0'||code.toCharArray()[p]<='9')
				return p;
			if(f)p++;
			else p--;
		}
		p=0;
		while(p<code.length())
		{
			if(code.toCharArray()[p]>='0'||code.toCharArray()[p]<='9')
				return p;
			p++;
		}
		return -1;
	}
	private String code_delete(String code,int r1,int r2) {
		if(r1+r2>=code.length())
			return code.substring(0,r1);
		return code.substring(0, r1)+code.substring(r1+r2);
	}
	
	private String replace(String a,String b,String c) {
		int pos=a.indexOf(b);
		return a.substring(0, pos)+c+a.substring(pos+b.length());
	}
	
	private int calLineNum(String info) {
		String[] items=info.split("----------");
		for(String item:items) if(item.contains("ERROR in")){

			int  p=item.indexOf("(at line ");
			p+=9;
			int res=0;
			while(item.charAt(p)!=')') {
				res=res*10+item.charAt(p)-'0';
				p++;
			}
			return res;
		}
		return -1;
	}
	
	private String getClasspath(String path) {
		String res="";
		File f=new File(path);
		String[] files=f.list();
		for(String file : files)
			res+=path+"\\"+file+";";
		return res;
	}
	public int random_search_keyword (String code)
	{
		Random r=new Random();
		int i,j=0,p=0;
		boolean f=true;
		do {
			i=r.nextInt(code.length());
			j=r.nextInt(key.length);
			if(code.substring(i).contains(key[j]))
			{
				p=code.indexOf(key[j],i);
				f=false;
				break;
			}
			}
		while(f);
		return p;
	}
	public boolean word(char x)
	{
		if(x<='z'&&x>='a'||x>='A'&&x<='Z')
			return true;
		else
			return false;
	}
	public int search_wordtail(String code, int p)
	{
		int t=p+1;
		for(;t<code.length();t++)
		{
			if(!word(code.toCharArray()[t]))
				break;
		}
		if(t>=code.length())
			t=code.length()-1;
		return t;
	}
	public int random_search_character (String code)
	{
		Random r=new Random();
		int i,j=0,p=0;
		boolean f=true;
		do {
			i=r.nextInt(code.length());
			j=r.nextInt(token.length);
			if(code.substring(i).contains(token[j]))
			{
				p=code.indexOf(token[j],i);
				f=false;
			}
			}
		while(f);
		return p;
	}
}




