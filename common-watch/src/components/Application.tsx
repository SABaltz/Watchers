import React, {useState} from "react";
import {BrowserRouter, Route, Routes} from "react-router-dom";
import NavBar from "./NavBar";
import Footer from "./Footer";
import HomePage from "./HomePage";
import Report from "./Report";
import List from "./List";

export const ProjectContext = React.createContext(null);

export default function Application({projectName, alternativeSite}) {
    return (
        <>
            <ProjectContext.Provider value={{ projectName: projectName, alternativeSite: alternativeSite }}>
                <NavBar/>
                <BrowserRouter>
                    <Routes>
                        <Route path="/" element={<HomePage/>}/>
                        <Route path="/report" element={<Report/>}/>
                        <Route path="/list" element={<List/>}/>
                    </Routes>
                </BrowserRouter>
                <Footer/>
            </ProjectContext.Provider>
        </>
    )
}
