# yolo-agda-gpt

(work in progress)


## Introduction and motivation 

The modest goal of this project is to provide a simple interface to ChatGPT for Agda.

It is aimed at proficient Agda users who wish to discharge proof obligations that are too boring or tedious to do "by hand."

This will improve the quality of life of the Agda developer, who is now free to focus on their *real* problems.

Generally speaking, this tool is not meant for beginners, since doing lots of simple things by hand in the beginning is an important part of learning the language.

## Installation and Usage

(work in progress)

At the moment, we have only tested the tool on a simple single-file module living within the `yolo-agda-gpt` directory.  To try it out in this simple setting, follow these steps:

1. Clone the repository and change to the `yolo-agda-gpt` directory.

   ```
   git clone git@github.com:marcinjangrzybowski/yolo-agda-gpt.git
   cd yolo-agda-gpt
   ```

2. Open the `YOLO-algebra-tests.agda` file in emacs.

3. Assuming you have `agda` and `agda-mode` installed, type-check the file and move the cursor to the first hole. 

4.  Type `yolo! 5` in the hole (where 5 is the number of tries you want to give ChatGPT) and enter the command `C-c C-m` to query to ChatGPT.

## How it works

TODO




