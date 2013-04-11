using System;
using System.Collections.Generic;
using System.Collections.ObjectModel;
using System.Collections.Specialized;
using System.Data;
using System.IO;
using System.Linq;
using System.Reflection;
using System.Text;
using System.Text.RegularExpressions;
using System.Threading;
using System.Threading.Tasks;
using System.Xml;
using System.Xml.Linq;
using System.Xml.Xsl;

using Microsoft.TeamFoundation.Client;
using Microsoft.TeamFoundation.Framework.Client;
using Microsoft.TeamFoundation.Framework.Common;
using Microsoft.TeamFoundation.VersionControl.Client;

using DotNetWikiBot;

namespace Locutus {
    class Program {
        private static string _xmlSavePath, _collectionName, _tfsServerUri, _workspacePath;
        private static string _wikiUrl, _wikiDomain, _wikiUser, _wikiPassword;
        private static List<WikiFilter> _wikiFilters;
        private static string[] _parsingScope;
        private static int _parsingThreadCount, _wikiThreadCount;
        private static bool _verbose, _wikiUpdate, _workspaceUpdate, _parsingUpdate;

        private static Queue<string> _files;
        private static Queue<Page> _pages;
        private static Mutex _lockNext, _lockSave, _lockRegister;
        private static XElement _doc;
        private static int _processed, _total;
        private static List<int> _runningThreads;
        
        private static Site _wiki;
        private struct _regex {
            public static Regex Namespace = new Regex(@"\s*namespace\s+([a-zA-Z0-9_\-.]+)\s*{([\s\S]*)}\s*$", RegexOptions.IgnoreCase);
            public static Regex References = new Regex(@"\s*using\s+([a-z.]+)\s*;", RegexOptions.IgnoreCase);
            public static Regex Classes = new Regex(@"((?:\s*///.*\n)+)?\s*(?:\[(.*)\])?\s*(public|private|protected|internal)?(?:\s+(static|partial|sealed))?\s+class\s+([a-zA-Z0-9\-_]+(?:<[a-zA-Z0-9\-_]+>)?)\s*(?::\s*([a-zA-Z0-9\-_.]+)\s*)?{([\s\S]*)}", RegexOptions.IgnoreCase);
            public static Regex Properties = new Regex(@"((?:\s*///.*\n)+)?\s*(?:\[(.*)\])?\s*(?:(public|private|protected|internal)\s+)(?:(static|override|delegate)*\s+)?(?:([a-zA-Z0-9\-_\[\].]+|<[a-zA-Z0-9\-_\[\]<>., ]+>)\s+)([a-zA-Z0-9\-_]+)\s*{(?=(?:(?:public|private|protected|internal)?\s*)+\s*(?:get|set) {)+", RegexOptions.IgnoreCase);
            public static Regex Accessors = new Regex(@"((?:public|private|protected|internal)?\s*)?\s*(get|set) {", RegexOptions.IgnoreCase);
            public static Regex Methods = new Regex(@"((?:\s*///.*\n)+)?\s*(?:\[(.*)\])?\s*(?:(public|private|protected|internal)\s+)(?:(static|override|delegate)*\s+)?(?:([a-zA-Z0-9\-_\[\].]+|<[a-zA-Z0-9\-_\[\]<>., ]+>)\s+)?([a-zA-Z0-9\-_]+)\s*\((?:((?:[a-zA-Z0-9\-_\[\].]+|<[a-zA-Z0-9\-_\[\]<>., ]+>)\s+[a-zA-Z0-9\-_]+),?\s*)*\)\s*{", RegexOptions.IgnoreCase);
            public static Regex Headers = new Regex(@"^\s*///\s*(.+)$", RegexOptions.Multiline | RegexOptions.IgnoreCase);
            public static Regex ReservedChars = new Regex(@"[\[\]{}<>]");
            public static Regex EmptyLines = new Regex(@"(?:\s*\r?\n){3,}", RegexOptions.Multiline);
        }

        public static void Main(string[] args) {
            LoadConfig("config.xml");

            _runningThreads = new List<int>();

            _lockNext = new Mutex();
            _lockSave = new Mutex();
            _lockRegister = new Mutex();

            if(_workspaceUpdate)
                UpdateWorkspace(_tfsServerUri, _workspacePath);

            if (_parsingUpdate) {
                FindSourceFiles(_workspacePath);

                _doc = new XElement("collection");
                _doc.Add(new XAttribute("name", _collectionName));
                _processed = 0;
                _total = _files.Count;

                ParameterizedThreadStart work = new ParameterizedThreadStart(ParseFile);
                for (int i = 0; i < _parsingThreadCount; i++) {
                    Thread thread = new Thread(work);
                    thread.Start(i);
                }
            }
            else {
                XmlDocument dom = new XmlDocument();
                dom.Load(_xmlSavePath);

                if(_wikiUpdate)
                    SaveToWiki(dom, dom);
            }
        }

        #region thread

        private static string GetNextFile() {
            string nextFile = null;

            _lockNext.WaitOne();

            if (_files.Count > 0)
                nextFile = _files.Dequeue();

            _lockNext.ReleaseMutex();

            return nextFile;
        }

        private static Page GetNextPage() {
            Page nextPage = null;

            _lockNext.WaitOne();

            if (_pages.Count > 0)
                nextPage = _pages.Dequeue();

            _lockNext.ReleaseMutex();

            return nextPage;
        }

        private static void SaveDoc(XElement doc) {
            _lockSave.WaitOne();

            MergeElements(_doc, doc);

            Console.Clear();
            Console.Write("Parsed: {0}/{1}... ", ++_processed, _total);

            if (_verbose)
                Console.WriteLine(_doc);
            
            _lockSave.ReleaseMutex();
        }

        private static void RegisterThread(int number, bool register) {
            _lockRegister.WaitOne();

            if (register)
                _runningThreads.Add(number);
            else {
                _runningThreads.Remove(number);

                if (_files.Count == 0 && _runningThreads.Count == 0) {
                    Console.WriteLine("done.");

                    XmlDocument oldDom = new XmlDocument();
                    oldDom.Load(_xmlSavePath);

                    XmlDocument newDom = new XmlDocument();
                    newDom.LoadXml(_doc.ToString());

                    File.WriteAllText(_xmlSavePath, _doc.ToString(), ASCIIEncoding.ASCII);

                    if(_wikiUpdate)
                        SaveToWiki(oldDom, newDom);
                }
            }

            _lockRegister.ReleaseMutex();
        }

        private static void ParseFile(object oThreadNumber) {
            int threadNumber = (int)oThreadNumber;
            string path;
            XElement xRoot;
            List<string> ancestry;
            string contents;

            RegisterThread(threadNumber, true);

            while ((path = GetNextFile()) != null) {
                contents = File.ReadAllText(path);
                contents = contents.Replace("\r", string.Empty);
                ancestry = new List<string>(path.Replace(_workspacePath, string.Empty).Split('\\'));

                ancestry.RemoveAt(ancestry.Count - 1);
                if (ancestry[0] == string.Empty)
                    ancestry.RemoveAt(0);
                
                //ParseReferences(contents);
                xRoot = ParseCollection(ancestry, contents);

                SaveDoc(xRoot);
            }

            RegisterThread(threadNumber, false);
        }

        private static void SavePage(object oThreadNumber) {
            int threadNumber = (int)oThreadNumber;
            Page page;

            while ((page = GetNextPage()) != null) {
                if (FilterWikiTitles(page.title)) {
                    if (page.text == string.Empty)
                        page.text = "No documentation generated from source control.";

                    page.Save(page.text, "Update from source control", false);
                }
            }
        }

        #endregion

        #region tfs

        private static void UpdateWorkspace(string tfsUri, string workspacePath) {
            string repository = "$/";
            string workspaceName = string.Format("{0} - Locutus Workspace", System.Environment.MachineName);

            Uri uri = new Uri(tfsUri);
            TfsTeamProjectCollection tfs = TfsTeamProjectCollectionFactory.GetTeamProjectCollection(uri);
            VersionControlServer vcs = (VersionControlServer)tfs.GetService(typeof(VersionControlServer));

            Workspace[] workspaces = vcs.QueryWorkspaces(workspaceName, vcs.AuthorizedUser, Workstation.Current.Name);
            if (workspaces.Length > 0)
                vcs.DeleteWorkspace(workspaceName, vcs.AuthorizedUser);

            Workspace workspace = vcs.CreateWorkspace(workspaceName, vcs.AuthorizedUser, "Locutus Temporary Workspace");
            WorkingFolder folder = new WorkingFolder(repository, workspacePath);

            workspace.CreateMapping(folder);
            Console.Write("getting files... ");
            workspace.Get();
            Console.WriteLine("done.");
        }

        private static void FindSourceFiles(string path) {
            List<string> files = new List<string>(Directory.GetFiles(_workspacePath, "*.cs", SearchOption.AllDirectories));

            List<string> notFiles = new List<string>(files);
            foreach (string file in notFiles)
                if (file.EndsWith("designer.cs"))
                    files.Remove(file);

            _files = new Queue<string>(files);
        }

        #endregion

        #region parsing

        private static void ParseReferences(string s) {
            MatchCollection matches = _regex.References.Matches(s);
            foreach (Match match in matches) {
                if (match.Success) {
                    Console.WriteLine("dependency: {0}", match.Groups[1].Value);
                }
            }
        }

        private static XElement ParseCollection(List<string> ancestry, string contents) {
            XElement xRoot = new XElement("collection");
            xRoot.Add(new XAttribute("name", _collectionName));

            ParseTeamprojects(ancestry, xRoot, contents);

            return xRoot;
        }

        private static void ParseTeamprojects(List<string> ancestry, XElement xRoot, string s) {
            XElement xTeamproject = new XElement("teamproject");
            xTeamproject.Add(new XAttribute("name", ancestry[0]));
            xRoot.Add(xTeamproject);

            ancestry.RemoveAt(0);
            ParseNamespaces(ancestry, xTeamproject, s);
        }

        private static void ParseNamespaces(List<string> ancestry, XElement xTeamproject, string s) {
            Match match = _regex.Namespace.Match(s);
            if (match.Success) {
                XElement xNew, xPrev;
                List<string> nss = new List<string>(match.Groups[1].Value.Split('.'));
                //TODO: parse namespace headers
                List<string> ancestryNoCase = new List<string>();
                foreach (string ancestor in ancestry)
                    ancestryNoCase.Add(ancestor.ToLower());

                xPrev = xTeamproject;

                int i;
                foreach (string ns in nss) {
                    i = ancestryNoCase.IndexOf(ns.ToLower());
                    if (i >= 0) {
                        ancestry.RemoveRange(i, ancestry.Count - i);
                        ancestryNoCase.RemoveRange(i, ancestryNoCase.Count - i);
                    }
                }

                foreach (string ns in ancestry) {
                    xNew = new XElement("namespace");
                    xNew.Add(new XAttribute("name", ns.Replace(" ", string.Empty)));

                    xPrev.Add(xNew);
                    xPrev = xNew;
                }

                foreach (string ns in nss) {
                    xNew = new XElement("namespace");
                    xNew.Add(new XAttribute("name", ns));

                    xPrev.Add(xNew);
                    xPrev = xNew;
                }

                ParseClasses(xPrev, match.Groups[2].Value);
            }
        }

        private static void ParseClasses(XElement xNamespace, string s) {
            MatchCollection matches = _regex.Classes.Matches(s);

            foreach (Match match in matches) {
                if (match.Success) {
                    if (_parsingScope.Contains(match.Groups[3].Value)) {
                        XElement xClass = new XElement("class");

                        ParseHeaders(xClass, match.Groups[1].Value);

                        if (match.Groups[2].Value.Length > 0)
                            xClass.Add(new XElement("attribute", match.Groups[2].Value));

                        if (match.Groups[3].Value.Length > 0)
                            xClass.Add(new XElement("scope", match.Groups[3].Value));

                        if (match.Groups[4].Value.Length > 0)
                            xClass.Add(new XElement("modifiers", match.Groups[4].Value));

                        xClass.Add(new XAttribute("name", match.Groups[5].Value));

                        if (match.Groups[6].Value.Length > 0)
                            xClass.Add(new XAttribute("baseclass", match.Groups[6].Value));

                        ParseProperties(xClass, match.Groups[7].Value);
                        ParseMethods(xClass, match.Groups[7].Value);

                        xNamespace.Add(xClass);
                    }
                }
            }
        }

        private static void ParseProperties(XElement xClass, string s) {
            MatchCollection matches = _regex.Properties.Matches(s);
            XElement xAccessor, xAccessors, xProperty, xProperties = null;

            foreach (Match match in matches) {
                if (match.Success) {
                    xProperty = new XElement("property");
                    
                    ParseHeaders(xProperty, match.Groups[1].Value);

                    if (match.Groups[2].Value.Length > 0)
                        xProperty.Add(new XElement("attribute", match.Groups[2].Value));

                    if (match.Groups[3].Value.Length > 0)
                        xProperty.Add(new XElement("scope", match.Groups[3].Value));

                    if (match.Groups[4].Value.Length > 0)
                        xProperty.Add(new XElement("modifiers", match.Groups[4].Value));

                    if (xProperty.Element("returntype") == null)
                        xProperty.Add(new XElement("returntype", match.Groups[5].Value));

                    xProperty.Add(new XAttribute("name", match.Groups[6].Value));

                    int start = s.IndexOf(match.Value) + match.Value.Length;
                    int i = start;
                    int openBraces = 1;
                    
                    while (openBraces > 0 && i < s.Length) {
                        switch(s[i]){
                            case '{':
                                openBraces++;
                                break;
                            case '}':
                                openBraces--;
                                break;
                        }

                        i++;
                    }

                    string contents = s.Substring(start, i - start - 1);

                    xAccessors = null;
                    MatchCollection accessors = _regex.Accessors.Matches(contents);
                    foreach (Match accessor in accessors) {
                        xAccessor = new XElement("accessor");

                        if (accessor.Groups[1].Value.Trim().Length > 0)
                            xAccessor.Add(new XElement("scope", accessor.Groups[1].Value));

                        xAccessor.Add(new XAttribute("name", accessor.Groups[2].Value));

                        if (xAccessors == null)
                            xAccessors = new XElement("accessors");

                        xAccessors.Add(xAccessor);
                    }

                    if (xAccessors != null)
                        xProperty.Add(xAccessors);

                    if (xProperties == null)
                        xProperties = new XElement("properties");

                    xProperties.Add(xProperty);
                }
            }

            if (xProperties != null)
                xClass.Add(xProperties);
        }

        private static void ParseMethods(XElement xClass, string s) {
            MatchCollection matches = _regex.Methods.Matches(s);
            XElement xMethod, xMethods = null;
            XAttribute xAttribute;
            
            foreach (Match match in matches) {
                if (match.Success) {
                    xMethod = new XElement("method");

                    ParseHeaders(xMethod, match.Groups[1].Value);

                    if(match.Groups[2].Value.Length > 0)
                        xMethod.Add(new XElement("attribute", match.Groups[2].Value));

                    if(match.Groups[3].Value.Length > 0)
                        xMethod.Add(new XElement("scope", match.Groups[3].Value));

                    if (match.Groups[4].Value.Length > 0)
                        xMethod.Add(new XElement("modifiers", match.Groups[4].Value));
                    
                    if(xMethod.Element("returntype") == null)
                        xMethod.Add(new XElement("returntype", match.Groups[5].Value));

                    xMethod.Add(new XAttribute("name", match.Groups[6].Value));

                    if (match.Groups[7].Value.Length > 0) {
                        Dictionary<string, string> parameters = new Dictionary<string, string>();
                        foreach (Capture capture in match.Groups[7].Captures) {
                            string[] p = capture.Value.Split(' ');
                            if (p.Length == 2)
                                parameters.Add(p[1], p[0]);
                        }

                        IEnumerable<XElement> xParameters = xMethod.Descendants("param");
                        if (xParameters.Count<XElement>() > 0) {
                            foreach (XElement xParam in xParameters) {
                                if (parameters.ContainsKey(xParam.Attribute("name").Value)) {
                                    if ((xAttribute = xParam.Attribute("type")) == null)
                                        xParam.Add(new XAttribute("type", parameters[xParam.Attribute("name").Value]));
                                    else
                                        xAttribute.Value = parameters[xParam.Attribute("name").Value];
                                }
                            }
                        }
                        else { //no parameters found in headers
                            if (xMethod.Element("nullparams") == null) {
                                XElement xParams = new XElement("params");

                                XElement xParam;
                                foreach (KeyValuePair<string, string> parameter in parameters) {
                                    xParam = new XElement("param");
                                    xParam.Add(new XAttribute("name", parameter.Key));
                                    xParam.Add(new XAttribute("type", parameter.Value));
                                    xParams.Add(xParam);
                                }

                                xMethod.Add(xParams);
                            }
                        }
                    }

                    if (xMethods == null)
                        xMethods = new XElement("methods");

                    xMethods.Add(xMethod);
                }
            }

            if (xMethods != null)
                xClass.Add(xMethods);
        }

        private static void ParseHeaders(XElement xMember, string s) {
            s = _regex.Headers.Replace(s, @"$1");
            if (s.Length > 0) {
                try {
                    XmlDocument headers = new XmlDocument();
                    headers.LoadXml(string.Format("<headers>{0}</headers>", s));

                    string value;
                    XElement xHeader, xParams = null;
                    XmlElement element;
                    foreach (XmlNode node in headers.DocumentElement.ChildNodes) {
                        if (node.GetType() == typeof(XmlElement)) {
                            element = (XmlElement)node;

                            value = element.InnerXml.Trim();
                            switch (element.LocalName) {
                                case "param":
                                    if (xParams == null)
                                        xParams = new XElement("params");

                                    xHeader = new XElement("param", value);
                                    foreach (XmlAttribute attribute in element.Attributes)
                                        xHeader.Add(new XAttribute(attribute.LocalName, attribute.Value));

                                    if(xHeader.Attribute("name") == null)
                                        xHeader.Add(new XAttribute("name", "UnnamedParam"));

                                    xParams.Add(xHeader);
                                    break;
                                case "returns":
                                    if (node.Attributes["type"] != null) {
                                        xHeader = new XElement("returntype", node.Attributes["type"].Value);
                                        xMember.Add(xHeader);
                                    }

                                    try {
                                        XmlDocument doc = new XmlDocument();
                                        doc.LoadXml(value);
                                        value = string.Format("<pre>\n{0}\n</pre>", PrettyXml(value).Replace(" ", "&nbsp;"));
                                    }
                                    catch (Exception) { }

                                    xHeader = new XElement(element.LocalName, value);
                                    xMember.Add(xHeader);
                                    break;
                                case "summary":
                                    if (value.Trim() != "///") {
                                        xHeader = new XElement(element.LocalName, value);
                                        xMember.Add(xHeader);
                                    }
                                    break;
                                default:
                                    xHeader = new XElement(element.LocalName, value);
                                    xMember.Add(xHeader);
                                    break;
                            }
                        }
                    }

                    if (xParams != null)
                        xMember.Add(xParams);
                }
                catch (Exception) { }
            }
        }

        #endregion

        #region wiki

        private static void SaveToWiki(XmlDocument domOld, XmlDocument domNew) {
            _wiki = new Site(_wikiUrl, _wikiUser, _wikiPassword, _wikiDomain);
            Console.WriteLine();

            List<Page> oldPages = new List<Page>();
            GetWikiPages(oldPages, _collectionName, domOld.DocumentElement);

            List<Page> newPages = new List<Page>();
            GetWikiPages(newPages, _collectionName, domNew.DocumentElement);

            PurgeWikiPages(oldPages, newPages);

            Console.WriteLine("{0} pages to import... ", newPages.Count);

            _pages = new Queue<Page>(newPages);
            ParameterizedThreadStart work = new ParameterizedThreadStart(SavePage);
            for (int i = 0; i < _wikiThreadCount; i++) {
                Thread thread = new Thread(work);
                thread.Start(i);
            }
        }

        private static void GetWikiPages(List<Page> pages, string pageName, XmlElement xPage) {
            XmlElement element;
            XmlAttribute name;

            string link;

            Page page = new Page(_wiki);
            page.title = _regex.ReservedChars.Replace(pageName, "-");
            page.text = string.Empty;
            pages.Add(page);

            page.text = BuildPage(xPage.LocalName, pageName, xPage);

            foreach (XmlNode node in xPage.ChildNodes) {
                if (node.GetType() == typeof(XmlElement)) {
                    element = (XmlElement)node;

                    if (element.LocalName == "methods") {
                        foreach (XmlElement method in element.SelectNodes("./method")) {
                            if ((name = method.Attributes["name"]) != null) {
                                if (method.SelectSingleNode("scope") == null || _parsingScope.Contains(method.SelectSingleNode("scope").InnerText)) {
                                    link = BuildMethodLink(page.title, method);
                                    link = link.Substring(2, link.IndexOf('|') - 2);

                                    if (_verbose)
                                        Console.WriteLine(link);

                                    GetWikiPages(pages, link, method);
                                }
                            }
                        }
                    }
                    else if (element.Attributes["name"] != null) {
                        if (element.SelectSingleNode("scope") == null || _parsingScope.Contains(element.SelectSingleNode("scope").InnerText)) {
                            link = string.Format("{0}.{1}", page.title, element.Attributes["name"].Value);

                            if (_verbose)
                                Console.WriteLine(link);

                            GetWikiPages(pages, link, element);
                        }
                    }
                }
            }
        }

        private static void PurgeWikiPages(List<Page> oldPages, List<Page> newPages) {
            foreach (Page page in newPages)
                oldPages.RemoveAll(p => p.title == page.title);

            foreach (Page page in oldPages) {
                try {
                    page.Delete("Page purged by Source Control");
                }
                catch (WikiBotException) { }
            }
        }

        private static string BuildPage(string type, string ns, XmlElement xPage) {
            string template = GetEmbededFile("Templates.page.template");
            Dictionary<string, string> vars = new Dictionary<string, string>() {
                {"name", xPage.Attributes["name"].Value},
                {"ancestry", BuildAncestry(ns)},
                {"details", string.Empty},
                {"description", SafeSelectNode(xPage, "./summary")},
                {"scope", SafeSelectNode(xPage, "./scope")},
                {"modifiers", SafeSelectNode(xPage, "./modifiers")},
                {"content", string.Empty},
                {"date", string.Format("{0:yyyy-MM-dd HH:mm:ss}", DateTime.Now)}
            };

            switch (xPage.LocalName) {
                case "method":
                    vars["pagetype"] = "Method";
                    vars["content"] = BuildMethodPage(ns, xPage);
                    break;
                case "class":
                    vars["pagetype"] = "Class";
                    vars["content"] = BuildClassPage(ns, xPage);
                    break;
                case "namespace":
                    vars["pagetype"] = "Namespace";
                    vars["content"] = BuildNamespacePage(ns, xPage);
                    break;
                case "teamproject":
                    vars["pagetype"] = "TeamProject";
                    vars["content"] = BuildTeamProjectPage(ns, xPage);
                    break;
                case "collection":
                    vars["pagetype"] = "Collection";
                    vars["content"] = BuildCollectionPage(ns, xPage);
                    break;
                default:
                    throw new Exception("unknown page type");
            }

            if (vars["scope"] != string.Empty || vars["modifiers"] != string.Empty) {
                string[] modifiers = (vars["scope"] + " " + vars["modifiers"]).Trim().Split(' ');

                if (modifiers.Length > 0) {
                    string pieceTemplate = GetEmbededFile("Templates.details.piece.template");
                    foreach (string modifier in modifiers)
                        vars["details"] += BuildString(pieceTemplate, "modifier", modifier.ToUpper());

                    vars["details"] = vars["details"].Remove(vars["details"].Length - 2, 2);
                    int index = vars["details"].IndexOf(',');
                    if (index > -1)
                        vars["details"] = vars["details"].Remove(index, 1).Insert(index, " and");

                    string sectionTemplate = GetEmbededFile("Templates.details.section.template");
                    vars["details"] = BuildString(sectionTemplate, new Dictionary<string, string>(){
                        {"type", vars["pagetype"].ToLower()},
                        {"modifiers", vars["details"]}
                    });
                }

                vars["modifiers"] = vars["modifiers"].ToUpper();
            }

            template = BuildString(template, vars);
            template = _regex.EmptyLines.Replace(template, "\r\n\r\n", 1);

            return template;
        }

        private static string BuildCollectionPage(string ns, XmlElement xPage) {
            string template = GetEmbededFile("Templates.collection.page.template");
            Dictionary<string, string> vars = new Dictionary<string, string>() {
                {"name", xPage.Attributes["name"].Value},
                {"teamprojects", string.Empty}
            };

            Dictionary<string, string> sectionVars;
            string section, sectionTemplate = GetEmbededFile("Templates.teamproject.section.template");
            foreach (XmlElement xSection in xPage.SelectNodes("./teamproject")) {
                sectionVars = new Dictionary<string, string>() {
                    {"name", xSection.Attributes["name"].Value},
                    {"link", string.Format("{0}.{1}", ns, xSection.Attributes["name"].Value)},
                    {"countNamespaces", xSection.SelectNodes(".//namespace").Count.ToString()},
                    {"countClasses", xSection.SelectNodes(".//class").Count.ToString()},
                    {"countMethods", xSection.SelectNodes(".//method").Count.ToString()}
                };

                section = BuildString(sectionTemplate, sectionVars);
                vars["teamprojects"] = string.Format("{0}\n\n{1}", vars["teamprojects"], section);
            }

            template = BuildString(template, vars);

            return template;
        }

        private static string BuildTeamProjectPage(string ns, XmlElement xPage) {
            string template = GetEmbededFile("Templates.teamproject.page.template");
            Dictionary<string, string> vars = new Dictionary<string, string>() {
                {"name", xPage.Attributes["name"].Value},
                {"namespaces", string.Empty}
            };

            Dictionary<string, string> sectionVars;
            string sectionTemplate = GetEmbededFile("Templates.namespace.piece.template");
            foreach (XmlElement xSection in xPage.SelectNodes("./namespace")) {
                sectionVars = new Dictionary<string, string>() {
                    {"name", xSection.Attributes["name"].Value},
                    {"link", BuildLink(string.Format("{0}.{1}", ns, xSection.Attributes["name"].Value), xSection.Attributes["name"].Value)},
                    {"countNamespaces", xSection.SelectNodes("./namespace").Count.ToString()},
                    {"countClasses", xSection.SelectNodes("./class").Count.ToString()},
                    {"description", SafeSelectNode(xSection, "./summary")},
                    {"classes", string.Empty},
                    {"namespaces", string.Empty}
                };

                //classes
                foreach (XmlElement xClass in xSection.SelectNodes("./class"))
                    sectionVars["classes"] += string.Format("*{0}\n", BuildLink(string.Format("{0}.{1}.{2}", ns, sectionVars["name"], xClass.Attributes["name"].Value), xClass.Attributes["name"].Value));
                
                //namespaces
                foreach (XmlElement xNamespace in xSection.SelectNodes("./namespace"))
                    sectionVars["namespaces"] += string.Format("*{0}\n", BuildLink(string.Format("{0}.{1}.{2}", ns, sectionVars["name"], xNamespace.Attributes["name"].Value), xNamespace.Attributes["name"].Value));

                vars["namespaces"] += BuildString(sectionTemplate, sectionVars);
            }

            template = BuildString(template, vars);

            return template;
        }

        private static string BuildNamespacePage(string ns, XmlElement xPage) {
            string template = GetEmbededFile("Templates.namespace.page.template");
            Dictionary<string, string> vars = new Dictionary<string, string>() {
                {"name", xPage.Attributes["name"].Value},
                {"sections", string.Empty}
            };

            int i;
            List<string> sections = new List<string>();
            SortedDictionary<string, string> sort;
            Dictionary<string, string> pieceVars, sectionVars;
            string section, piece, sectionTemplate, pieceTemplate;

            //classes
            i = 0;
            sort = new SortedDictionary<string, string>();
            pieceTemplate = GetEmbededFile("Templates.class.piece.template");
            foreach (XmlElement xSection in xPage.SelectNodes("./class")) {
                pieceVars = new Dictionary<string, string>() {
                    {"name", xSection.Attributes["name"].Value},
                    {"link", BuildLink(string.Format("{0}.{1}", ns, xSection.Attributes["name"].Value), xSection.Attributes["name"].Value)},
                    {"countMethods", xSection.SelectNodes(".//method").Count.ToString()},
                    {"modifiers", SafeSelectNode(xSection, "./modifiers")},
                    {"description", SafeSelectNode(xSection, "./summary")}
                };

                piece = BuildString(pieceTemplate, pieceVars);
                sort.Add(string.Format("{0}-{1}", pieceVars["name"], i++), piece);
            }

            section = string.Empty;
            foreach (KeyValuePair<string, string> item in sort)
                section = string.Format("{0}\n\n{1}", section, item.Value);

            if (section != string.Empty) {
                sectionVars = new Dictionary<string, string>(){
                    {"classes", section}
                };

                sectionTemplate = GetEmbededFile("Templates.class.section.template");
                sections.Add(BuildString(sectionTemplate, sectionVars));
            }

            //namespaces
            i = 0;
            sort = new SortedDictionary<string, string>();
            pieceTemplate = GetEmbededFile("Templates.namespace.piece.template");
            foreach (XmlElement xSection in xPage.SelectNodes("./namespace")) {
                pieceVars = new Dictionary<string, string>() {
                    {"name", xSection.Attributes["name"].Value},
                    {"link", BuildLink(string.Format("{0}.{1}", ns, xSection.Attributes["name"].Value), xSection.Attributes["name"].Value)},
                    {"countNamespaces", xSection.SelectNodes("./namespace").Count.ToString()},
                    {"countClasses", xSection.SelectNodes("./class").Count.ToString()},
                    {"countMethods", xSection.SelectNodes("./method").Count.ToString()},
                    {"description", SafeSelectNode(xSection, "./summary")}
                };

                piece = BuildString(pieceTemplate, pieceVars);
                sort.Add(string.Format("{0}-{1}", pieceVars["name"], i++), piece);
            }

            section = string.Empty;
            foreach (KeyValuePair<string, string> item in sort)
                section = string.Format("{0}\n\n{1}", section, item.Value);

            if (section != string.Empty) {
                sectionVars = new Dictionary<string, string>(){
                    {"namespaces", section}
                };

                sectionTemplate = GetEmbededFile("Templates.namespace.section.template");
                sections.Add(BuildString(sectionTemplate, sectionVars));
            }

            foreach (string s in sections)
                vars["sections"] += string.Format("{0}\n\n", s);

            template = BuildString(template, vars);

            return template;
        }

        private static string BuildClassPage(string ns, XmlElement xPage) {
            string template = GetEmbededFile("Templates.class.page.template");
            Dictionary<string, string> vars = new Dictionary<string, string>() {
                {"name", xPage.Attributes["name"].Value},
                {"sections", string.Empty}
            };

            List<string> sections = new List<string>();
            Dictionary<string, string> sectionVars, pieceVars;
            Dictionary<string, SortedDictionary<string, string>> methodSections;
            SortedDictionary<string, string> sort;
            string section, piece, sectionTemplate, pieceTemplate, scope, key;
            int i;

            //properties
            i = 0;
            sort = new SortedDictionary<string, string>();
            pieceTemplate = GetEmbededFile("Templates.property.piece.template");
            foreach (XmlElement xSection in xPage.SelectNodes("./properties/property")) {
                sectionVars = new Dictionary<string, string>() {
                    {"name", xSection.Attributes["name"].Value},
                    {"returntype", SafeSelectNode(xSection, "./returntype")},
                    {"scope", SafeSelectNode(xSection, "./scope")},
                    {"description", SafeSelectNode(xSection, "./summary")},
                    {"accessors", string.Empty}
                };

                foreach (XmlElement xAccessor in xSection.SelectNodes("./accessors/accessor")) {
                    scope = SafeSelectNode(xAccessor, "./scope");
                    if (_parsingScope.Contains(scope) || (scope == string.Empty && _parsingScope.Contains(sectionVars["scope"])))
                        sectionVars["accessors"] += string.Format("{0}/", xAccessor.Attributes["name"].Value);
                }

                sectionVars["accessors"] = sectionVars["accessors"].TrimEnd('/');

                section = BuildString(pieceTemplate, sectionVars);
                sort.Add(string.Format("{0}-{1}", sectionVars["name"], i++), section);
            }

            section = string.Empty;
            sectionTemplate = GetEmbededFile("Templates.property.section.template");
            foreach (KeyValuePair<string, string> item in sort)
                section = string.Format("{0}\n\n{1}", section, item.Value);

            if (section != string.Empty)
                sections.Add(BuildString(sectionTemplate, "properties", section));

            //methods
            i = 0;
            methodSections = new Dictionary<string, SortedDictionary<string, string>>();
            pieceTemplate = GetEmbededFile("Templates.method.piece.template");
            foreach (XmlElement xSection in xPage.SelectNodes("./methods/method")) {
                if (_parsingScope.Contains(SafeSelectNode(xSection, "./scope"))) {
                    pieceVars = new Dictionary<string, string>() {
                        {"name", xSection.Attributes["name"].Value},
                        {"link", BuildMethodLink(ns, xSection)},
                        {"scope", SafeSelectNode(xSection, "./scope")},
                        {"modifiers", SafeSelectNode(xSection, "./modifiers")},
                        {"returntype", SafeSelectNode(xSection, "./returntype")},
                        {"description", SafeSelectNode(xSection, "./summary")}
                    };

                    piece = BuildString(pieceTemplate, pieceVars);

                    key = pieceVars["scope"] + " " + pieceVars["modifiers"];
                    if(!methodSections.ContainsKey(key))
                        methodSections.Add(key, new SortedDictionary<string, string>());

                    methodSections[key].Add(string.Format("{0}-{1}-{2}", (pieceVars["returntype"] == string.Empty ? "0-" : string.Empty) + pieceVars["name"], pieceVars["link"], i++), piece);
                }
            }

            section = string.Empty;
            sectionTemplate = GetEmbededFile("Templates.method.section.template");
            foreach (KeyValuePair<string, SortedDictionary<string, string>> methodSection in methodSections) {
                sectionVars = new Dictionary<string, string>() {
                    {"modifiers", methodSection.Key.ToUpper()},
                    {"methods", string.Empty}
                };

                foreach (KeyValuePair<string, string> item in methodSection.Value)
                    sectionVars["methods"] = string.Format("{0}\n\n{1}", sectionVars["methods"], item.Value);

                section = string.Format("{0}\n\n{1}", section, BuildString(sectionTemplate, sectionVars));
            }

            if (section != string.Empty)
                sections.Add(section);

            foreach (string s in sections)
                vars["sections"] = string.Format("{0}\n\n{1}", vars["sections"], s);

            template = BuildString(template, vars);

            return template;
        }

        private static string BuildMethodPage(string ns, XmlElement xPage) {
            string template = GetEmbededFile("Templates.method.page.template");
            Dictionary<string, string> vars = new Dictionary<string, string>() {
                {"name", xPage.Attributes["name"].Value},
                {"returntype", SafeSelectNode(xPage, "./returntype")},
                {"returns", SafeSelectNode(xPage, "./returns")},
                {"parameters", string.Empty}
            };

            string[] yesReqs = new string[] { "yes", "true" };
            Dictionary<string, string> sectionVars;
            string required;
            string section, sectionTemplate = GetEmbededFile("Templates.parameter.section.template");
            foreach (XmlElement xSection in xPage.SelectNodes("./params/param")) {
                sectionVars = new Dictionary<string, string>() {
                    {"name", xSection.Attributes["name"].Value},
                    {"type", SafeSelectAttribute(xSection, "type", "unknown")},
                    {"required", (yesReqs.Contains(SafeSelectAttribute(xSection, "required").ToLower()) ? "required" : " ")},
                    {"description", xSection.InnerText}
                };

                required = SafeSelectAttribute(xSection, "required");
                if (required.Length > 0) {
                    if (yesReqs.Contains(required.ToLower()))
                        sectionVars["required"] = "required";
                    else
                        sectionVars["required"] = string.Format("required {0}", required);

                }

                section = BuildString(sectionTemplate, sectionVars);
                vars["parameters"] = string.Format("{0}\n\n{1}", vars["parameters"], section);
            }

            if (vars["returntype"] == string.Empty)
                vars["returntype"] = "n/a";

            if (vars["parameters"] == string.Empty)
                vars["parameters"] = "none";

            template = BuildString(template, vars);

            return template;
        }

        private static string BuildLink(string title, string name) {
            title = _regex.ReservedChars.Replace(title, "-");

            if (title.Length > 255)
                title = title.Substring(0, 255);

            return string.Format("[[{0}|{1}]]", title, name);
        }

        private static string BuildMethodLink(string ns, XmlElement xMethod){
            string link = string.Empty;
            string parameters, signature, returntype, name, type;

            name = SafeSelectAttribute(xMethod, "name");
            returntype = SafeSelectNode(xMethod, "./returntype");

            parameters = string.Empty;
            signature = string.Empty;
            foreach (XmlElement xParameter in xMethod.SelectNodes(".//param")) {
                type = SafeSelectAttribute(xParameter, "type", "unknown");
                parameters += string.Format("{0} {1}, ", type, xParameter.Attributes["name"].Value);
                signature += string.Format("{0}, ", type);
            }

            signature = string.Format("{0}.{1}({2})", ns, name, signature.Replace(", ", ",").TrimEnd(','));
            parameters = string.Format("{0} ({1})", name, parameters.TrimEnd(new char[] { ',', ' ' }));

            link = BuildLink(signature, parameters); 

            return link;
        }

        private static string BuildAncestry(string ns) {
            string ancestory = string.Empty;

            string[] spaces = ns.Split('.');
            string link = string.Empty;
            foreach (string s in spaces) {
                link += string.Format("{0}.", s);
                ancestory += string.Format("{0}.", BuildLink(link.TrimEnd('.'), s));
            }

            return ancestory.TrimEnd('.');
        }

        private static bool FilterWikiTitles(string title) {
            if (_wikiFilters.Count > 0) {
                foreach (WikiFilter filter in _wikiFilters)
                    if (filter.Check(title))
                        return true;

                return false;
            }
            else
                return true;
        }

        #endregion

        #region helpers

        private static void LoadConfig(string configFile) {
            XmlDocument config = new XmlDocument();
            config.Load(configFile);

            _collectionName = config.SelectSingleNode("//collectionname").InnerText;
            _xmlSavePath = config.SelectSingleNode("//outputpath").InnerText;

            _tfsServerUri = config.SelectSingleNode("//tfs/url").InnerText;
            _workspaceUpdate = bool.Parse(config.SelectSingleNode("//tfs/update").InnerText);
            _workspacePath = config.SelectSingleNode("//tfs/workspacepath").InnerText;

            _parsingUpdate = bool.Parse(config.SelectSingleNode("//parsing/update").InnerText);
            _parsingScope = config.SelectSingleNode("//parsing/scope").InnerText.Split(' ');
            _parsingThreadCount = int.Parse(config.SelectSingleNode("//parsing/threads").InnerText);

            _wikiUpdate = bool.Parse(config.SelectSingleNode("//wiki/update").InnerText);
            _wikiUrl = config.SelectSingleNode("//wiki/url").InnerText;
            _wikiDomain = config.SelectSingleNode("//wiki/domain").InnerText;
            _wikiUser = config.SelectSingleNode("//wiki/user").InnerText;
            _wikiPassword = config.SelectSingleNode("//wiki/password").InnerText;
            _wikiThreadCount = int.Parse(config.SelectSingleNode("//wiki/threads").InnerText);

            _wikiFilters = new List<WikiFilter>();
            foreach (XmlElement xFilter in config.SelectSingleNode("//wiki/filters").ChildNodes)
                _wikiFilters.Add(new WikiFilter((WikiFilter.FilterType)Enum.Parse(typeof(WikiFilter.FilterType), xFilter.LocalName, true), xFilter.InnerText));

            _verbose = bool.Parse(config.SelectSingleNode("//rundetails/verbose").InnerText);
        }

        private static string SafeSelectNode(XmlElement element, string xpath) {
            return (element.SelectSingleNode(xpath) == null ? string.Empty : element.SelectSingleNode(xpath).InnerText);
        }

        private static string SafeSelectAttribute(XmlElement element, string attribute) {
            return SafeSelectAttribute(element, attribute, string.Empty);
        }

        private static string SafeSelectAttribute(XmlElement element, string attribute, string notFound) {
            return (element.Attributes[attribute] == null ? notFound : element.Attributes[attribute].Value);
        }

        private static bool AreEquivalent(XElement a, XElement b) {
                if (a.Name != b.Name) return false;
                if (!a.HasAttributes && !b.HasAttributes) return true;
                if (!a.HasAttributes || !b.HasAttributes) return false;
                if (a.Attributes().Count() != b.Attributes().Count()) return false;

                return a.Attributes().All(attA => b.Attributes(attA.Name).Count(attB => attB.Value == attA.Value) != 0);
        }

        private static void MergeElements(XElement parentA, XElement parentB) {
            bool isMatchFound;
            XElement childB, childA;

            foreach (XNode nodeB in parentB.Elements()) {
                isMatchFound = false;

                if (nodeB.GetType() == typeof(XElement)) {
                    childB = (XElement)nodeB;

                    foreach (XNode nodeA in parentA.Elements()) {
                        if (nodeA.GetType() == typeof(XElement)) {
                            childA = (XElement)nodeA;

                            if (AreEquivalent(childA, childB)) {
                                MergeElements((XElement)childA, (XElement)childB);
                                isMatchFound = true;
                                break;
                            }
                        }
                    }

                    if (!isMatchFound)
                        parentA.Add(childB);
                }
            }
        }

        private static string ReadHiddenString() {
            string s = string.Empty;
            ConsoleKeyInfo key;

            do {
                key = Console.ReadKey(true);

                if (key.Key != ConsoleKey.Backspace && key.Key != ConsoleKey.Enter) {
                    s += key.KeyChar;
                    Console.Write("*");
                }
                else {
                    if (key.Key == ConsoleKey.Backspace && s.Length > 0) {
                        s = s.Substring(0, (s.Length - 1));
                        Console.Write("\b \b");
                    }
                }
            }
            while (key.Key != ConsoleKey.Enter);
            Console.WriteLine();
            return s;
        }

        private static string PrettyXml(string xml) {
            string pretty = "";

            MemoryStream mStream = new MemoryStream();
            XmlTextWriter writer = new XmlTextWriter(mStream, Encoding.Unicode);
            XmlDocument document = new XmlDocument();

            try {
                document.LoadXml(xml);
                writer.Formatting = Formatting.Indented;

                document.WriteContentTo(writer);
                writer.Flush();
                mStream.Flush();

                mStream.Position = 0;

                StreamReader sReader = new StreamReader(mStream);

                pretty = sReader.ReadToEnd();
            }
            catch (XmlException) {}

            mStream.Close();
            writer.Close();

            return pretty;
        }

        public static string BuildString(string s, string var, string val) {
            if (s != null && var != null) {
                if (val == null)
                    val = "";

                s = s.Replace("{" + var + "}", val);
            }

            return s;
        }

        private static string BuildString(string s, Dictionary<string, string> vars) {
            if (s != null)
                foreach (KeyValuePair<string, string> var in vars)
                    s = BuildString(s, var.Key, var.Value);

            return s;
        }

        public static string GetEmbededFile(string name) {
            Assembly assembly = Assembly.GetExecutingAssembly();
            string assemblyName = assembly.FullName.Split(',')[0];
            Stream stream = assembly.GetManifestResourceStream(string.Format("{0}.{1}", assemblyName, name));

            if (stream == null)
                throw new Exception(string.Format("Resource '{0}' not found in assembly '{1}'", name, assemblyName));

            StreamReader reader = new StreamReader(stream);

            return reader.ReadToEnd();
        }

        private class WikiFilter {
            private FilterType _type;
            private string _filter;

            public enum FilterType{
                Contains,
                Equals
            }

            public WikiFilter(FilterType type, string filter) {
                _type = type;
                _filter = filter;
            }

            public bool Check(string s) {
                bool check = true;

                if(_type == FilterType.Equals)
                    check = (_filter == s);
                if(_type == FilterType.Contains)
                    check = s.Contains(_filter);

                return check;
            }
        }

        #endregion
    }
}