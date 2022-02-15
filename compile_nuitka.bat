call venv_py3\Scripts\activate.bat
python -m nuitka --standalone --plugin-enable=multiprocessing --plugin-enable=pylint-warnings --mingw64 .\clcache
pushd conan
set CONAN_REVISIONS_ENABLED=1
conan export-pkg conanfile.py --force
conan upload clcache/* --all -r globus
popd
pause

